module Lab9 where

import Data.Array
import Data.List
import qualified Data.Map as Map
import Data.Maybe

{-------------------------------------------------------------------------------

LAB 9: Automata

DUE: Thursday, April 26, 11:59 PM

This lab asks you to explore finite automata and compilation of regular
expressions.

SUBMISSION INSTRUCTIONS: Submit only Lab9.hs.  Do not submit any of your test
data, &c.

-------------------------------------------------------------------------------}

{-------------------------------------------------------------------------------

PART 1: DFAs

In this part, we build DFAs to recognize strings. Our representation of DFAs
uses a 2-dimensional array, indexed by states (Ints) and input characters.
Remember that the array access operator in Haskell is spelled `!`; for example,
for a DFA `d` to get the output for state 0 and input character 'A', you would
get `dfaTransitions d ! (0, 'A')`. We restrict the input alphabet to the capital
letters.

You should write the accepts function, which takes a DFA and a String and
returns True if the input string is accepted by the provided DFA, and returns
False otherwise.

FOR EXTRA CREDIT: write the longest function, which takes a DFA and a String and
returns a pair of the longest substring accepted by the DFA and the remaining
characters.  (Note that this is not quite what we do for lexing: there we need
to know the accept state as well.)

-------------------------------------------------------------------------------}


data DFA = DFA { dfaStart :: Int, dfaTransitions :: Array (Int, Char) Int, dfaFinal :: [Int] }
  deriving (Show)

noTransitions :: [Int] -> Int -> [Int] -> DFA
noTransitions states start final =
    DFA start (listArray ((smallest, 'A'), (largest, 'Z')) (repeat (-1))) final
    where smallest = minimum states
          largest = maximum states

addTransition :: Int -> Char -> Int -> DFA -> DFA
addTransition start symbol end dfa =
    dfa{ dfaTransitions = dfaTransitions dfa // [((start, symbol), end)] }

accepts :: DFA -> String -> Bool
accepts = error "unimplemented"

longest :: DFA -> String -> (String, String)
longest = error "extra credit"

{-------------------------------------------------------------------------------

PART 2: NFAs

In this part, we build NFAs to recognize strings.  As before, we restrict the
input alphabet to the capital letters.  Our representation here is more suited
to constructing NFAs than to checking strings: we represent the transitions as a
simple list of [(input state, character, output state)].  Nothing cases in the
transitions correspond to epsilon transitions.

You should write the nfaAccepts function, which takes an NFA and a String and
returns True if the input string is accepted by the provided DFA, and False
otherwise.

You may find the provided epsClose function helpful.  This function returns all
states reachable by epsilon transitions from the given state.

-------------------------------------------------------------------------------}

data NFA = NFA { nfaStart :: Int, nfaTransitions :: [(Int, Maybe Char, Int)], nfaFinal :: [Int] }
  deriving (Show)

epsClose :: NFA -> Int -> [Int]
epsClose nfa s = iter [s]
    where iter ss
              | all (`elem` ss) ts = ss
              | otherwise = iter ts
              where ts = nub ([t | (s, Nothing, t) <- nfaTransitions nfa, s `elem` ss] ++ ss)

nfaAccepts :: NFA -> String -> Bool
nfaAccepts = error "unimplemented"


{-------------------------------------------------------------------------------

INTERLUDE: Converting NFAs to DFAs

(Nothing for you to do here.)

-------------------------------------------------------------------------------}


determinize :: NFA -> DFA
determinize nfa =
    Map.foldrWithKey (\(ss, c) ts -> addTransition (ixFor ss) c (ixFor ts))
                     (noTransitions (map snd stateIxs)
                                    (ixFor startStates)
                                    [i | (ss, i) <- stateIxs, any (`elem` nfaFinal nfa) ss])
                     edges

    where transitions = nfaTransitions nfa
          transitionsFrom ss = nub [c | (s, Just c, t) <- transitions, s `elem` ss]
          step ss c = nub $ concatMap (epsClose nfa) $ [t | (s, Just d, t) <- transitions, c == d, s `elem` ss]
          iter visited [] edges = (visited, edges)
          iter visited (ss : sss) edges
              | ss `elem` visited = iter visited sss edges
              | otherwise = iter (ss : visited) (map snd steps ++ sss) edges'
              where cs = transitionsFrom ss
                    steps = [(c, sort (step ss c)) | c <- cs]
                    edges' = foldr (\(c, ts) -> Map.insert (ss, c) ts) edges steps

          startStates = sort (epsClose nfa (nfaStart nfa))
          (states, edges) = iter [] [startStates] Map.empty
          stateIxs = zip states [1..]
          ixFor s = fromJust (lookup s stateIxs)

{-------------------------------------------------------------------------------

PART 3: Compiling regular expressions

Finally, you should write the compile function, which takes a regular expression
and produces an NFA.  Regular expressions are expressed using the RegEx type,
which has cases corresponding to standard grammar of regular expressions.  For
example, the following expresses a regex recognizing strings "A", "ABA",
"ABABA", etc.:

    Exact 'A' `Seq` Star (Exact 'B' `Seq` Exact 'A')

When compiling regular expressions, you will have to generate new states.  To
help with this, the compile function takes, as an argument, the first integer
available for new states.  It returns not just the constructed NFA, but also
then next new integer.  For example, if you called

    compile (Exact 'A') 1

then you should get back the pair

    (NFA 1 [(1, Just 'A', 2)] [2], 3)

We used states 1 and 2 to build the NFA, and so the next available state is 3.
Similarly, if you called

    compile Eps 24

Then you should get back the pair

    (NFA 24, [] [24], 25)

We used state 25 to build to NFA, and so the next available state is 25.  In
cases like Seq or Or, you will have to thread this "next available state"
parameter through the compilation of the other regular expressions.

-------------------------------------------------------------------------------}

data RegEx = Eps | Exact Char | Wild | Seq RegEx RegEx | Or RegEx RegEx | Star RegEx
  deriving (Eq, Show)

infixl 5 `Seq`
infixl 4 `Or`

compile :: RegEx -> Int -> (NFA, Int)
compile = error "unimplemented"

compile' :: RegEx -> NFA
compile' = fst . flip compile 0
