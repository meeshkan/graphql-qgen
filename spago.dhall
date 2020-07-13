{-
Welcome to a Spago project!
You can edit this file as you like.
-}
{ name = "runr"
, dependencies =
  [ "console"
  , "effect"
  , "graphql-gen"
  , "graphql-parser"
  , "graphql-validator"
  , "numbers"
  , "ordered-collections"
  , "profunctor-lenses"
  , "psci-support"
  , "unicode-prelude"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
