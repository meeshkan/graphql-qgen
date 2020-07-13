module Test.Gen where

import Prelude
import Control.Monad.Except (runExcept)
import Data.Either (either, isRight)
import Data.GraphQL.AST as AST
import Data.GraphQL.Parser as GP
import Data.GraphQL.RequestValidator (validateOperationDefinitionAgainstSchema)
import Data.List (filter, length)
import Data.Newtype (unwrap)
import Data.Traversable (sequence)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Generator.GraphQL (_n_a_WithSeedFrom_b, generateOperationDefinitionFromDocument)
import HackerNewsSchema (hackerNewsSchema)
import Prelude.Unicode ((⋘))
import Test.Spec (SpecT, before, describe, it)
import Test.Spec.Assertions (shouldEqual, fail)
import Text.Parsing.Parser (runParser)
import Text.Parsing.Parser.String (class StringLike)
import TwitterSchema (twitterSchema)

parseDocument ∷ ∀ s. StringLike s ⇒ s → Aff (AST.Document)
parseDocument t = liftEffect (either (throw <<< show) pure (runParser t GP.document))

doesOperationDefinitionHaveNonEmptySelectionSet ∷ AST.OperationDefinition → Boolean
doesOperationDefinitionHaveNonEmptySelectionSet (AST.OperationDefinition_OperationType ot) = length (unwrap ot.selectionSet) > 0

doesOperationDefinitionHaveNonEmptySelectionSet (AST.OperationDefinition_SelectionSet ss) = length (unwrap ss) > 0

schemaValidator ∷ forall m. Monad m ⇒ String → SpecT Aff Unit m Unit
schemaValidator schema =
  before (parseDocument schema)
    $ do
        it "generates correct operations for schema" \doc → do
          either
            (fail ⋘ show)
            ( \l → do
                length l `shouldEqual` 100
                length (filter (isRight ⋘ runExcept ⋘ flip validateOperationDefinitionAgainstSchema doc) l) `shouldEqual` 100
            )
            ( sequence
                $ _n_a_WithSeedFrom_b generateOperationDefinitionFromDocument doc 100 0
            )
        it "generates at least one non-empty selection set" \doc → do
          either
            (fail ⋘ show)
            ( \l → do
                length l `shouldEqual` 100
                ( ( length
                      $ filter doesOperationDefinitionHaveNonEmptySelectionSet l
                  )
                    > 1
                )
                  `shouldEqual`
                    true
            )
            ( sequence
                $ _n_a_WithSeedFrom_b generateOperationDefinitionFromDocument doc 100 0
            )

testGenerateSelectionSet ∷ ∀ m. Monad m ⇒ SpecT Aff Unit m Unit
testGenerateSelectionSet =
  describe "tests generation of operations" do
    describe "tests generation of operations for twitter" do
      schemaValidator twitterSchema
    describe "tests generation of operations for hacker news" do
      schemaValidator hackerNewsSchema
