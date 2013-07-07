{-# OPTIONS_GHC -Wall #-}

import Data.List


{-
    The abstract inference systems defined here are essentially just boring old inference systems
    over arbitrary structures that represent anything from bare propositions like A&B to hypothetical
    judgments like A, B !- C to logical relations like f $ x ---> y to even crazy things like
    Turing machine configurations like q2 @ 0011010[1]0011101.
    
    The primary data type of interest is the structures that are shuffled between inference rules.
    A structure can be either a typed metavariable, representing an unknown portion of the structure,
    or it can be a constructor applied to some arguments. Constructors have arities but are untyped.
    Metavariable types refer solely to the types in the subgrammars for structures. For instance,
    we might have two kinds of structures, variables and terms. Variables have the constructors
    vz and vs, basically coding the naturals, and terms include variables, but also have the tuple
    operations pair, for building pairs, and fst and snd for projecting. Thus we have the arities
    
      vz   :     -> *
      vs   :   * -> *
      pair : *,* -> *
      fst  :   * -> *
      snd  :   * -> *
    
    A structure is considered well formed if the constructors are applied to the correct number
    of arguments.
-}

type Name = String

data Arity = Arity { name :: Name, arity :: Int }
  deriving (Show,Eq)

type Signature = [Arity]

structureArity :: Signature -> Name -> Maybe Int
structureArity g n = do d <- find (\d -> name d == n) g
                        Just (arity d)

type Subtype = String

type Varname = Int

data Metavar = Metavar Varname Subtype
  deriving (Show,Eq)

data Structure = Var Metavar | Structure Name [Structure]
  deriving (Show,Eq)

wellFormedStructure :: Signature -> Structure -> Bool
wellFormedStructure _ (Var _)          = True
wellFormedStructure g (Structure n bs) = case structureArity g n of
                                 Nothing -> False
                                 Just a  -> length bs == a && all (wellFormedStructure g) bs

freeMetavars :: Structure -> [Metavar]
freeMetavars (Var v)          = [v]
freeMetavars (Structure _ bs) = nub (concatMap freeMetavars bs)




{-
    We also want to express the subgrammar that defines valid ("grammatical") subsets of
    the well-formed structures. A grammar consists of a number of sybtype clauses
    of the form
      
      type ::= form | form | ...
    
    Each form is either a bare subtype name, as in the first clause if
    
      var
      
    or consists of a constructor name and a list of forms, representing the constructor
    applied to some arguments, as in
    
      pair term term
      
    Thus we might have the grammar
    
      var ::= vz | vs var
      term ::= var | pair term term | fst term | snd term
      
    that expresses the grammaticality of the terms that can be built from the previously
    mentioned collection of constructors. We also, of course, want to be able to figure out
    when a structure is a member of a class of structures defined by some type in the
    grammar for a language, so we have the relevant test function. This probably makes
    well-formedness and arities superfluous.
-}

data GrammarForm = GrammarSubtype Subtype | GrammarForm Name [GrammarForm]
  deriving (Show,Eq)

data GrammarSubtypeDef = GrammarSubtypeDef { subtype :: Subtype, forms :: [GrammarForm] }
  deriving (Show,Eq)

type Grammar = [GrammarSubtypeDef]

formsForSubtype :: Grammar -> Subtype -> Maybe [GrammarForm]
formsForSubtype g t = do cs <- find (\cs -> subtype cs == t) g
                         Just (forms cs)

checkSubtype :: Grammar -> Subtype -> Structure -> Bool
checkSubtype g t b = case formsForSubtype g t of
                       Nothing -> False
                       Just cs -> tryForms g b cs

matchGrammarForm :: Grammar -> GrammarForm -> Structure -> Bool
matchGrammarForm _ (GrammarSubtype t) (Var (Metavar _ t')) = t == t'
matchGrammarForm g (GrammarSubtype t) (Structure n' bs')   = checkSubtype g t (Structure n' bs')
matchGrammarForm _ (GrammarForm _ _)  (Var _)              = False
matchGrammarForm g (GrammarForm n bs) (Structure n' bs')   = n == n' && and (zipWith (matchGrammarForm g) bs bs')

tryForms :: Grammar -> Structure -> [GrammarForm] -> Bool
tryForms _ _ []     = False
tryForms g b (c:cs) = matchGrammarForm g c b || tryForms g b cs




{-
    To do proofs in an abstract inference system, we need to be able to think of
    inference rules as being abstract patterns over structures. These patterns ought
    to have variables that specify the grammatical form that it matches against, which
    we will represent as a question-marked grammatical type followed by a number, as in
    
      ?term0
    
    For example, the standard inference rule for conjunction introduction might be
    rendered (using infix notation for structure constructor names) as
    
      ?ctx0 !- ?prop0   ?ctx0 !- ?prop1
      --------------------------------- &I
          ?ctx0 !- ?prop0 & ?prop1
          
    Which would, in more common notation, be something like
    
      G !- A   G !- B
      --------------- &I
         G !- A & B
    
    These structures, as conclusions, must be unified with the premise patterns of the
    partial proof that is intended to extend below (working bottom up), and so we need
    to have a syntactic unification mechanism to allow a (possibly variable-containing)
    structure like
    
      <> !- A & B
      
    to be matched against a conclusion pattern (almost certainly containing variables)
    such as
    
      ?ctx0 !- ?prop0 & ?prop1
      
    so that the substition, in this case { ?ctx0 -> <>, ?prop0 -> A, ?prop1 -> B }, can be
    used to instantiate the premises for further proof search. We also of course need
    a means of merging substitutions from the sub-structure unifications. It is probably
    ideal to modify the merge function here to fully instantiate all occurances of a variable
    in the unifier when the variable's value is determined. I haven't added this yet, however.
-}

type Substitution a = [(Metavar,a)]

substitutionVars :: Substitution a -> [Metavar]
substitutionVars sub = map fst sub

instantiateVariable :: Eq a => Metavar -> Structure -> Substitution a -> Maybe (Substitution a)
instantiateVariable v s sub = undefined

merge :: Eq a => Substitution a -> Substitution a -> Maybe (Substitution a)
merge [] t'        = Just t'
merge ((v,a):t) t' = case lookup v t of
                       Nothing -> do t'' <- merge t t'
                                     Just $ (v,a):t''
                       Just a' -> if a == a'
                                  then do t'' <- merge t (t' \\ [(v,a)])
                                          Just $ (v,a):t''
                                  else Nothing

mergeMultiple :: Eq a => [Substitution a] -> Maybe (Substitution a)
mergeMultiple []     = Just []
mergeMultiple (t:ts) = do t' <- mergeMultiple ts
                          merge t t'

unifyStructures :: Grammar -> Structure -> Structure -> Maybe (Substitution Structure)
unifyStructures g (Var (Metavar v t)) s' = if checkSubtype g t s'
                                          then Just [(Metavar v t, s')]
                                          else Nothing
unifyStructures g s (Var (Metavar v' t')) = if checkSubtype g t' s
                                           then Just [(Metavar v' t', s)]
                                           else Nothing
unifyStructures g (Structure n bs) (Structure n' bs')
  | n == n'   = do subs <- sequence (zipWith (unifyStructures g) bs bs')
                   mergeMultiple subs
  | otherwise = Nothing

substituteStructure :: Substitution Structure -> Structure -> Maybe Structure
substituteStructure sub (Var v)          = lookup v sub
substituteStructure sub (Structure n bs) = do bs' <- sequence (map (substituteStructure sub) bs)
                                              Just (Structure n bs')


                                           

{-
    Inference rules are now as you'd expect. We need some facility for refreshing the
    variables of an inference rule to prevent unintended capture when doing unification.
    We also need convenient ways of matching a whole rule and instantiating it as well.
    These are conveniences for defining the proof search.
-}

type RuleName = String

data InferenceRule = InferenceRule { ruleName :: RuleName, premises :: [Structure], conclusion :: Structure }
  deriving (Show,Eq)

freeMetavarsInferenceRule :: InferenceRule -> [Metavar]
freeMetavarsInferenceRule (InferenceRule _ ps c) = nub (concatMap freeMetavars ps ++ freeMetavars c)

refreshVars :: [Metavar] -> InferenceRule -> InferenceRule
refreshVars vs (InferenceRule n ps c) = InferenceRule n (map go ps) (go c)
  where maxVar = foldr (\(Metavar v _) i -> max v i) 0 vs
        varsLookup = zip vs [ v | v <- [maxVar+1..]]
        go (Var (Metavar v t)) = case lookup (Metavar v t) varsLookup of
                       Nothing -> Var (Metavar v t)
                       Just v' -> Var (Metavar v' t)
        go (Structure n' bs) = Structure n' (map go bs)

matchInferenceRule :: Grammar -> InferenceRule -> Structure -> Maybe (Substitution Structure)
matchInferenceRule g r s = unifyStructures g (conclusion r) s

instantiateInferenceRule :: InferenceRule -> Substitution Structure -> Maybe InferenceRule
instantiateInferenceRule (InferenceRule n ps c) sub = do ps' <- sequence (map (substituteStructure sub) ps)
                                                         c' <- substituteStructure sub c
                                                         Just (InferenceRule n ps' c')

type ProofSystem = [InferenceRule]




{-
    Lastly, we have the proof search. To prove a structure given some proof system and some
    substitutions from previously-found proofs, we try each combination of rule and substitution.
    Trying an inference rule just means matching it against the structure in question, and then
    trying to prove all of the premises. However we need to manage variable refreshing. Proving
    all the premises is just proving them one at a time, rippling the resulting substitutions
    through to the remaining premises. We also probably want a way to limit search depth, and so
    we have a counter for depth. Unlimited search depth can obviously be achieved by starting
    proof search with a negative number.
-}

proveStructure :: Integer -> Grammar -> ProofSystem -> [Substitution Structure] -> Structure -> [Substitution Structure]
proveStructure 0 _ _   _    _ = []
proveStructure n g sys subs s = do r <- sys
                                   sub <- subs
                                   tryInferenceRule n g sys sub r s                                     

tryInferenceRule :: Integer -> Grammar -> ProofSystem -> Substitution Structure -> InferenceRule -> Structure -> [Substitution Structure]
tryInferenceRule n g sys sub r s = case (newSubs,newPremises) of
                                     (Just sub'', Just ps') -> proveStructures n g sys sub'' ps'
                                     _ -> []
  where oldVars = substitutionVars sub
        refreshed = refreshVars oldVars r
        ruleSubs = matchInferenceRule g refreshed s
        newSubs = do sub' <- ruleSubs
                     merge sub sub'
        newPremises = do subs'' <- newSubs
                         sequence (map (substituteStructure subs'') (premises r))
                     

proveStructures :: Integer -> Grammar -> ProofSystem -> Substitution Structure -> [Structure] -> [Substitution Structure]
proveStructures _ _ _   sub []     = [sub]
proveStructures n g sys sub (p:ps) = do premiseSub <- proveStructure (n-1) g sys [sub] p
                                        proveStructures n g sys premiseSub ps




{-
    We can now test the system so far. Note that this just tests the grammar portion.
    Everything else is up for grabs right now!
-}

signature :: Signature
signature = [ Arity "vz" 0   -- vz   : -> *
            , Arity "vs" 1   -- vs   : * -> *
            , Arity "pair" 2 -- pair : *,* -> *
            , Arity "fst" 1  -- fst  : * -> *
            , Arity "snd" 1  -- snd  : * -> *
            ]

grammar :: Grammar
grammar = [ GrammarSubtypeDef "var" [ GrammarForm "vz" []                     -- var ::= vz
                                    , GrammarForm "vs" [GrammarSubtype "var"] --       | vs var
                                    ]
          , GrammarSubtypeDef "term" [ GrammarSubtype "var"                                                   -- term ::= var
                                     , GrammarForm "pair" [GrammarSubtype "term", GrammarSubtype "term"] --        | pair term term
                                     , GrammarForm "fst" [GrammarSubtype "term"]                         --        | fst term
                                     , GrammarForm "snd" [GrammarSubtype "term"]                         --        | snd term
                                     ]
          ]

vzB :: Structure
vzB = Structure "vz" []

vsB :: Structure -> Structure
vsB n = Structure "vs" [n]

pairB :: Structure -> Structure -> Structure
pairB a b = Structure "pair" [a,b]

fstB :: Structure -> Structure
fstB p = Structure "fst" [p]

sndB :: Structure -> Structure
sndB p = Structure "snd" [p]

goodStructure :: Structure
goodStructure = fstB (pairB vzB (vsB vzB))

badStructure :: Structure
badStructure = vsB (fstB (vzB))

main :: IO ()
main = putStr $ show $ ( wellFormedStructure signature goodStructure , checkSubtype grammar "term" goodStructure
                       , wellFormedStructure signature badStructure ,  checkSubtype grammar "term" badStructure
                       )
