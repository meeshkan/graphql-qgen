module Generator.GraphQL where

import Prelude
import Control.Monad.Except (runExceptT, throwError)
import Control.Monad.Except.Trans (ExceptT)
import Control.Monad.Gen (Size, resize)
import Control.Monad.Gen.Common (genMaybe)
import Control.Monad.Reader (ask, runReaderT)
import Control.Monad.Reader.Trans (ReaderT)
import Control.Monad.Trans.Class (lift)
import Data.Array as A
import Data.Array.NonEmpty (fromArray, toNonEmpty)
import Data.Array.NonEmpty as DANE
import Data.Either (Either, either)
import Data.GraphQL.AST (EnumTypeDefinition(..), InputObjectTypeDefinition(..), InterfaceTypeDefinition(..), ObjectTypeDefinition(..), ScalarTypeDefinition(..), UnionTypeDefinition(..))
import Data.GraphQL.AST as AST
import Data.GraphQL.Gen (genOperationDefinition)
import Data.GraphQL.Lens (getAllMutationDefinitions, getAllQueryDefinitions, getAllSubscriptionDefinitions, lensToTypeDefinitions)
import Data.GraphQL.Parser as GP
import Data.Lens as L
import Data.List (List(..), zip, (:), catMaybes, take, fromFoldable, length)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (unwrap)
import Data.NonEmpty (NonEmpty(..))
import Data.Set as Set
import Data.String.CodeUnits (fromCharArray)
import Data.Traversable (sequence)
import Data.Tuple (Tuple(..), snd, uncurry)
import Data.Unfoldable (replicateA)
import Effect (Effect)
import Effect.Exception (Error, error)
import Prelude.Unicode ((⋘), (⤜), (⤛))
import Test.QuickCheck (arbitrary, mkSeed)
import Test.QuickCheck.Gen (Gen, arrayOf, elements, evalGen, listOf, oneOf, shuffle, sized, suchThat)
import Text.Parsing.Parser (runParser)

type GraphQLEnv
  = { typeDefinitions ∷ List AST.TypeDefinition }

type GenStack a
  = ExceptT Error (ReaderT GraphQLEnv Gen) a

-- a lift for our stack
liftN ∷ ∀ a. Gen a → GenStack a
liftN = lift ⋘ lift

exceptableList ∷ ∀ a. List (Either Error a) → GenStack (List a)
exceptableList Nil = liftN $ pure Nil

exceptableList (x : xs) = either throwError (\g → (exceptableList xs) ⤜ (\v → liftN $ pure (g : v))) x

genValueForArgumentFromTypeDefinition ∷ AST.TypeDefinition → String → GenStack AST.Value
genValueForArgumentFromTypeDefinition (AST.TypeDefinition_EnumTypeDefinition (AST.EnumTypeDefinition etd)) hint =
  maybe
    ( throwError
        $ error "Enums must have values defined if required as an argument type"
    )
    ( \(AST.EnumValuesDefinition l) →
        maybe (throwError $ error "Enums must have values defined if required as an argument type")
          ( \na →
              liftN
                $ oneOf
                    ( map
                        ( \(AST.EnumValueDefinition e) →
                            (pure ⋘ AST.Value_EnumValue) e.enumValue
                        )
                        $ DANE.toNonEmpty na
                    )
          )
          (DANE.fromFoldable l)
    )
    etd.enumValuesDefinition

genValueForArgumentFromTypeDefinition (AST.TypeDefinition_InputObjectTypeDefinition (AST.InputObjectTypeDefinition itd)) hint =
  maybe
    (liftN $ pure (AST.Value_ObjectValue (AST.ObjectValue Nil)))
    ( \(AST.InputFieldsDefinition l) → do
        res ←
          sequence
            $ map
                ( \(AST.InputValueDefinition d) →
                    Tuple <$> pure d.name <*> genValueForArgumentFromType d.type hint
                )
                l
        liftN
          $ pure
              ( AST.Value_ObjectValue
                  ( AST.ObjectValue
                      $ map
                          ( \(Tuple k v) →
                              -- nothing happens if the value is nullable, which we translate here as a null value
                              AST.Argument
                                { name: k
                                , value: fromMaybe (AST.Value_NullValue AST.NullValue) v
                                }
                          )
                          res
                  )
              )
    )
    itd.inputFieldsDefinition

genValueForArgumentFromTypeDefinition (AST.TypeDefinition_InterfaceTypeDefinition (AST.InterfaceTypeDefinition itd)) _ =
  throwError
    ( error $ "Impossible to use interface type "
        <> itd.name
        <> " as input to a query. Use an input type"
    )

genValueForArgumentFromTypeDefinition (AST.TypeDefinition_ObjectTypeDefinition otd) _ =
  throwError
    $ error "Impossible to use an object type as input to a query. Use an input type"

-- for now, we generate an arbitrary string
-- we can make this more intelligent later, ie emails for emails, etc
genValueForArgumentFromTypeDefinition (AST.TypeDefinition_ScalarTypeDefinition std) hint =
  liftN
    $ (AST.Value_StringValue <$> (AST.StringValue <$> arbitrary))

genValueForArgumentFromTypeDefinition (AST.TypeDefinition_UnionTypeDefinition (AST.UnionTypeDefinition utd)) _ =
  throwError
    $ error "Impossible to use a union type as input to a query. Use an input type"

genValueForArgumentFromStringTypeName ∷ String → String → GenStack AST.Value
genValueForArgumentFromStringTypeName s hint = case s of
  "Int" → AST.Value_IntValue <$> (AST.IntValue <$> liftN arbitrary)
  "Float" → AST.Value_FloatValue <$> (AST.FloatValue <$> liftN arbitrary)
  "String" → AST.Value_StringValue <$> (AST.StringValue <$> liftN arbitrary)
  "Boolean" → AST.Value_BooleanValue <$> (AST.BooleanValue <$> liftN arbitrary)
  "ID" → AST.Value_StringValue <$> (AST.StringValue <$> liftN genName)
  _ → findTypeInDocument s ⤜ (flip genValueForArgumentFromTypeDefinition hint)

asNothing ∷ ∀ a. GenStack (Maybe a)
asNothing = liftN $ pure Nothing

lpj ∷ ∀ a. a → GenStack (Maybe a)
lpj = lp ⋘ Just

lp ∷ ∀ a. a → GenStack a
lp = liftN ⋘ pure

asMaybe ∷ ∀ a. GenStack a → GenStack (Maybe a)
asMaybe = (⤛) lpj

resizeSizedGS ∷ ∀ a. (Int → Int) → (Size → GenStack a) → GenStack a
resizeSizedGS rf sf = do
  v ← ask
  res ← liftN $ (resize rf (sized \i → (runGenStack' v $ sf i)))
  either throwError (\a → lift (pure a)) res

listOnResizeSchedule ∷ ∀ a. GenStack a → GenStack (List a)
listOnResizeSchedule z = resizeSizedGS (\i → max 0 $ i - 1) (\i → replicateA i z)

perhapsMaybe ∷ GenStack (AST.Value) → GenStack (Maybe AST.Value)
perhapsMaybe gs = do
  ugh ← liftN $ (arbitrary ∷ Gen Number)
  if (ugh < 0.5) then asNothing else asMaybe gs

genValueAsArgumentFromNamedType ∷ AST.NamedType → String → GenStack (Maybe AST.Value)
genValueAsArgumentFromNamedType (AST.NamedType n) hint =
  perhapsMaybe
    (genValueForArgumentFromStringTypeName n hint)

genValueAsArgumentFromListType ∷ AST.ListType → String → GenStack AST.Value
genValueAsArgumentFromListType (AST.ListType l) hint = do
  listOfMaybeValues ← listOnResizeSchedule (genValueForArgumentFromType l hint)
  liftN
    $ pure
        ( AST.Value_ListValue
            (AST.ListValue (map (fromMaybe $ AST.Value_NullValue AST.NullValue) listOfMaybeValues))
        )

genMaybeValueAsArgumentFromListType ∷ AST.ListType → String → GenStack (Maybe AST.Value)
genMaybeValueAsArgumentFromListType l hint = perhapsMaybe $ genValueAsArgumentFromListType l hint

genValueForArgumentFromType ∷ AST.Type → String → GenStack (Maybe AST.Value)
genValueForArgumentFromType (AST.Type_NamedType n) hint = genValueAsArgumentFromNamedType n hint

genValueForArgumentFromType (AST.Type_ListType l) hint = genMaybeValueAsArgumentFromListType l hint

genValueForArgumentFromType (AST.Type_NonNullType (AST.NonNullType_NamedType (AST.NamedType n))) hint =
  Just
    <$> genValueForArgumentFromStringTypeName n hint

genValueForArgumentFromType (AST.Type_NonNullType (AST.NonNullType_ListType n)) hint =
  Just
    <$> genValueAsArgumentFromListType n hint

generateArgumentFromInputValueDefinition ∷ AST.InputValueDefinition → GenStack (Maybe AST.Argument)
generateArgumentFromInputValueDefinition (AST.InputValueDefinition ivd) = do
  nm ← liftN $ pure ivd.name
  v ← genValueForArgumentFromType ivd.type ivd.name -- we give the name as a hint
  liftN $ maybe (pure Nothing) (\x → pure $ (Just $ AST.Argument { name: nm, value: x })) v

generateArgumentsFromArgumentsDefinition ∷ AST.ArgumentsDefinition → GenStack (AST.Arguments)
generateArgumentsFromArgumentsDefinition (AST.ArgumentsDefinition l) = do
  initialMap ← sequence $ map generateArgumentFromInputValueDefinition l
  liftN $ (AST.Arguments <$> (pure ⋘ catMaybes) initialMap)

typeDefinitionHasName ∷ String → AST.TypeDefinition → Boolean
typeDefinitionHasName s (AST.TypeDefinition_EnumTypeDefinition (EnumTypeDefinition e)) = e.name == s

typeDefinitionHasName s (AST.TypeDefinition_InputObjectTypeDefinition (InputObjectTypeDefinition e)) = e.name == s

typeDefinitionHasName s (AST.TypeDefinition_InterfaceTypeDefinition (InterfaceTypeDefinition e)) = e.name == s

typeDefinitionHasName s (AST.TypeDefinition_ObjectTypeDefinition (ObjectTypeDefinition e)) = e.name == s

typeDefinitionHasName s (AST.TypeDefinition_ScalarTypeDefinition (ScalarTypeDefinition e)) = e.name == s

typeDefinitionHasName s (AST.TypeDefinition_UnionTypeDefinition (UnionTypeDefinition e)) = e.name == s

firstTypeDefinition ∷ String → List AST.TypeDefinition → Maybe (AST.TypeDefinition)
firstTypeDefinition s =
  L.firstOf
    ( L.traversed
        ⋘ L.filtered (typeDefinitionHasName s)
    )

findTypeInDocument ∷ String → GenStack AST.TypeDefinition
findTypeInDocument s = do
  v ← ask
  maybe (throwError $ error ("Could not find a type called " <> s <> " in the document")) (\a → lift $ pure a)
    (firstTypeDefinition s v.typeDefinitions)

generateSelectionSetFromMaybeFieldsDefinition ∷ Maybe AST.FieldsDefinition → GenStack (Maybe AST.SelectionSet)
generateSelectionSetFromMaybeFieldsDefinition =
  maybe
    asNothing
    -- a bit hackish as the lambda currently prevents us from a long fix operator...
    ( \(AST.FieldsDefinition x) →
        ( asMaybe (generateSelectionSetFromFieldDefinitions (map unwrap x))
        )
    )

generateInlineFragmentFromNamedType ∷ AST.NamedType → GenStack AST.InlineFragment
generateInlineFragmentFromNamedType nt@(AST.NamedType s) = do
  typeDefinition ← findTypeInDocument s
  map AST.InlineFragment $ { typeCondition: _, directives: _, selectionSet: _ }
    <$> lpj (AST.TypeCondition nt)
    <*> asNothing
    <*> ( (generateSelectionSetFromTypeDefinition typeDefinition)
          ⤜ (maybe (throwError $ error "Unions can only be done on object types") lp)
      )

generateInlineFragmentSelectionSetFromNamedTypes ∷ List AST.NamedType → GenStack AST.SelectionSet
generateInlineFragmentSelectionSetFromNamedTypes nts =
  AST.SelectionSet
    <$> sequence (map ((<$>) AST.Selection_InlineFragment ⋘ generateInlineFragmentFromNamedType) nts)

generateSelectionSetFromTypeDefinition ∷ AST.TypeDefinition → GenStack (Maybe AST.SelectionSet)
generateSelectionSetFromTypeDefinition (AST.TypeDefinition_EnumTypeDefinition etd) = pure Nothing -- no selection can be made on an enum

generateSelectionSetFromTypeDefinition (AST.TypeDefinition_InputObjectTypeDefinition iotd) =
  throwError
    $ error "Impossible to run a query, mutation or subscription and expect an input object back"

generateSelectionSetFromTypeDefinition (AST.TypeDefinition_InterfaceTypeDefinition (AST.InterfaceTypeDefinition itd)) = generateSelectionSetFromMaybeFieldsDefinition itd.fieldsDefinition

generateSelectionSetFromTypeDefinition (AST.TypeDefinition_ObjectTypeDefinition (AST.ObjectTypeDefinition otd)) = generateSelectionSetFromMaybeFieldsDefinition otd.fieldsDefinition

generateSelectionSetFromTypeDefinition (AST.TypeDefinition_ScalarTypeDefinition std) = pure Nothing -- no selection can be made on a scalar

generateSelectionSetFromTypeDefinition (AST.TypeDefinition_UnionTypeDefinition (AST.UnionTypeDefinition utd)) = do
  maybe
    asNothing
    (asMaybe ⋘ generateInlineFragmentSelectionSetFromNamedTypes ⋘ unwrap)
    utd.unionMemberTypes

generateSelectionSetFromTypeName ∷ String → GenStack (Maybe AST.SelectionSet)
generateSelectionSetFromTypeName s = case s of
  "Int" → asNothing
  "Float" → asNothing
  "String" → asNothing
  "Boolean" → asNothing
  "ID" → asNothing
  _ → findTypeInDocument s ⤜ generateSelectionSetFromTypeDefinition

-- we ignore the fact this is a list
-- as graphql selections ignore listness
generateSelectionSetFromListType ∷ AST.ListType → GenStack (Maybe AST.SelectionSet)
generateSelectionSetFromListType (AST.ListType l) = generateSelectionSetFromType l

generateSelectionSetFromType ∷ AST.Type → GenStack (Maybe AST.SelectionSet)
generateSelectionSetFromType (AST.Type_NamedType (AST.NamedType n)) = generateSelectionSetFromTypeName n

generateSelectionSetFromType (AST.Type_ListType l) = generateSelectionSetFromListType l

generateSelectionSetFromType (AST.Type_NonNullType (AST.NonNullType_NamedType (AST.NamedType n))) = generateSelectionSetFromTypeName n

generateSelectionSetFromType (AST.Type_NonNullType (AST.NonNullType_ListType l)) = generateSelectionSetFromListType l

generateFieldFromFieldDefinition ∷ String → AST.T_FieldDefinition → GenStack AST.Field
generateFieldFromFieldDefinition aliasName fd =
  map AST.Field $ { alias: _, name: _, arguments: _, directives: _, selectionSet: _ }
    <$> liftN (genMaybe $ pure aliasName)
    <*> lp fd.name
    <*> maybe asNothing (asMaybe ⋘ generateArgumentsFromArgumentsDefinition) fd.argumentsDefinition
    <*> asNothing -- for now, we do not use directives. need to find a way to enhance this...
    <*> generateSelectionSetFromType fd.type

generateSelectionFromFieldDefinition ∷ String → AST.T_FieldDefinition → GenStack AST.Selection
generateSelectionFromFieldDefinition aliasName fd = AST.Selection_Field <$> (generateFieldFromFieldDefinition aliasName fd)

generateSelectionSetFromFieldDefinitions ∷ List AST.T_FieldDefinition → GenStack AST.SelectionSet
generateSelectionSetFromFieldDefinitions fdd =
  resizeSizedGS (\i → max 0 $ i - 1)
    ( \i → do
        shuffled ← liftN $ shuffle (A.fromFoldable fdd)
        let
          ln = (max 1 i)
        let
          fieldDefs = take ln (fromFoldable shuffled)
        -- guarantee unique alias names
        aliasNames ← liftN $ suchThat (listOf ln genName) (\l → length l == Set.size (Set.fromFoldable l))
        AST.SelectionSet
          <$> ( sequence
                $ ( map
                      (uncurry generateSelectionFromFieldDefinition)
                      ( zip
                          aliasNames
                          fieldDefs
                      )
                  )
            )
    )

genName ∷ Gen String
genName =
  ( (<>)
      <$> (sequence [ (elements $ NonEmpty '_' (GP.lower <> GP.upper)) ])
      <*> (arrayOf (elements $ NonEmpty '_' (GP.lower <> GP.upper <> GP.digits)))
  )
    ⤜ (pure ⋘ fromCharArray)

generateOperationDefinitionAST ∷ AST.OperationType → List AST.T_FieldDefinition → GenStack AST.OperationDefinition
generateOperationDefinitionAST ot l =
  map AST.OperationDefinition_OperationType
    $ { operationType: _
      , name: _
      , variableDefinitions: _
      , directives: _
      , selectionSet: _
      }
    <$> lp ot
    <*> (liftN $ genMaybe genName)
    <*> asNothing
    <*> asNothing
    <*> generateSelectionSetFromFieldDefinitions l

generateOperationDefinitionFromDocumentString ∷ String → ExceptT Error Gen AST.OperationDefinition
generateOperationDefinitionFromDocumentString s = do
  either (throwError ⋘ error ⋘ show) generateOperationDefinitionFromDocument $ runParser s GP.document

runGenStack' ∷ ∀ a. GraphQLEnv → GenStack a → Gen (Either Error a)
runGenStack' d g = runReaderT (runExceptT g) d

runGenStack ∷ ∀ a. AST.Document → GenStack a → Gen (Either Error a)
runGenStack d g =
  runGenStack'
    { typeDefinitions: (L.toListOf lensToTypeDefinitions d) }
    g

generateOperationDefinitionFromDocument ∷ AST.Document → ExceptT Error Gen AST.OperationDefinition
generateOperationDefinitionFromDocument d = do
  let
    _allDefs =
      A.filter (\t → length (snd t) > 0)
        ( map ((#) d)
            [ Tuple AST.Query ⋘ getAllQueryDefinitions
            , Tuple AST.Mutation ⋘ getAllMutationDefinitions
            , Tuple AST.Subscription ⋘ getAllSubscriptionDefinitions
            ]
        )
  maybe (throwError $ error "Document does not contain any queries, mutations or subscriptions")
    ( \allDefs → do
        (Tuple operationType fieldDefinitions) ← lift (elements (toNonEmpty allDefs))
        res ← lift $ runGenStack d (generateOperationDefinitionAST operationType fieldDefinitions)
        either throwError (lift ⋘ pure) res
    )
    (fromArray _allDefs)

generateOperationDefinitionStringFromDocument ∷ AST.Document → ExceptT Error Gen String
generateOperationDefinitionStringFromDocument =
  ((⤛) (lift ⋘ genOperationDefinition))
    ⋘ generateOperationDefinitionFromDocument

generateOperationDefinitionStringFromDocumentString ∷ String → ExceptT Error Gen String
generateOperationDefinitionStringFromDocumentString =
  ( (⤛)
      ( lift
          ⋘ genOperationDefinition
      )
  )
    ⋘ generateOperationDefinitionFromDocumentString

_n_a_WithSeedFrom_b ∷ ∀ a b. (b → ExceptT Error Gen a) → b → Int → Int → List (Either Error a)
_n_a_WithSeedFrom_b f s n sd = evalGen (listOf n (runExceptT $ f s)) { newSeed: mkSeed sd, size: 3 }

_n_Effecta_WithSeedFrom_b ∷ ∀ a b. (b → ExceptT Error Gen a) → b → Int → Int → Effect (Array a)
_n_Effecta_WithSeedFrom_b f s n sd =
  either throwError (pure ⋘ A.fromFoldable)
    $ sequence (_n_a_WithSeedFrom_b f s n sd)

nOperationStringsWithSeedFromDocumentString ∷ String → Int → Int → Effect (Array String)
nOperationStringsWithSeedFromDocumentString =
  _n_Effecta_WithSeedFrom_b
    generateOperationDefinitionStringFromDocumentString

nOperationsWithSeedFromDocumentString ∷ String → Int → Int → Effect (Array AST.OperationDefinition)
nOperationsWithSeedFromDocumentString = _n_Effecta_WithSeedFrom_b generateOperationDefinitionFromDocumentString
