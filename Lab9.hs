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
accepts d (s:ss) =  checkIfinFinal (concatMap (intcharIndfaTransitions d (head(intcharIndfaTransitions d (getDFAStart d) s)) ) ss) (getDFAfinalStates d)--trying to concatMap dfaTransitions on ss's to get all states. Not sure if that's possible. 
                                                                                                   -- I will next check if that list is in in the dfaFinal 
intcharIndfaTransitions :: DFA -> Int -> Char -> [Int]
intcharIndfaTransitions d i c = [dfaTransitions d ! (i,c)]

getDFAfinalStates :: DFA -> [Int]
getDFAfinalStates (DFA{ dfaFinal = n}) = n


getDFAStart :: DFA -> Int
getDFAStart (DFA{ dfaStart = s }) = s                    


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
nfaAccepts n (s:ss) = checkIfinFinal (concatMap (checkTransitions n (checkTransitions n (epsClose n (getNFAStart n)) s)) ss) (getFinalStates n)

checkIfinFinal :: [Int] -> [Int] -> Bool
checkIfinFinal l1 l2 = if (nub(l1 ++ l2) == (l1 ++ l2)) then True else False

getFinalStates :: NFA -> [Int]
getFinalStates (NFA {nfaFinal = n}) = n

checkTransitions :: NFA -> [Int] -> Char -> [Int]
checkTransitions NFA { nfaTransitions = tlist} is c = (lookupPairInTriple (intChartuples is c) tlist)

{--

THESE FUNCTIONS ARE LEFT HERE AS A MEMORY TO MY MANY ATTEMPTS AT THIS PROBLEM. THEY ARE NOW BANISHED TO THE DEAD ZONE!!!

intChartuples :: [Int] -> Char -> [(Int, Char)]
intChartuples (i:is) c = [(i,c)] ++ intChartuples is c

lookupPairInTriple :: (Eq a) => (Eq b) => [(a,b)] -> [(a,Maybe b,a)] -> [a]
lookupPairInTriple ((i,s):restp) ((i1,s2,i2):rest) = if ((i == i1) && (s == fromJust s2)) then [i2] ++ lookupPairInTriple restp rest else lookupPairInTriple restp rest

getNFAStart :: NFA -> Int
getNFAStart (NFA {nfaStart = s}) = s 

isFinalStateInList :: Ord a => [a] -> [a] -> Bool
isFinalStateInList cs fs = if ((nub (cs ++ fs)) == (cs ++ fs)) then True else False

getNFATransitions :: NFA -> [(Int, Maybe Char, Int)]
getNFATransitions (NFA {nfaTransitions = t}) = t

lookupTransitions :: Maybe Char -> Int -> [(Int, Maybe Char, Int)] -> Int
lookupTransitions inpChar curState ((cs, ic, ns):rest) = if (curState == cs && (inpChar == ic || ic == Nothing)) then ns else lookupTransitions inpChar curState rest


--}


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
compile (Eps) n = (NFA { nfaStart = n, nfaTransitions = [(n, Nothing, n+1)], nfaFinal = [n+1] }, n+2)--(NFA n [] [n], n+1)
compile (Exact a) n = (NFA { nfaStart = n, nfaTransitions = [(n, Just a, n+1)], nfaFinal = [n+1] }, n+2)--(NFA n [(n, Just a, n+1)] [n+1], n+2)
compile (Wild) n = (NFA {nfaStart = n, nfaTransitions = [(n, Just 'A', n + 1),(n, Just 'B', n+1),(n, Just 'C', n + 1),(n, Just 'D', n+1),(n, Just 'E', n + 1),(n, Just 'F', n+1),(n, Just 'G', n + 1),(n, Just 'H', n+1),(n, Just 'I', n + 1),(n, Just 'J', n+1),(n, Just 'K', n + 1),(n, Just 'L', n+1),(n, Just 'M', n + 1),(n, Just 'N', n+1),(n, Just 'O', n + 1),(n, Just 'P', n+1),(n, Just 'Q', n + 1),(n, Just 'R', n+1),(n, Just 'S', n + 1),(n, Just 'T', n+1),(n, Just 'U', n + 1),(n, Just 'V', n+1),(n, Just 'W', n + 1),(n, Just 'X', n+1),(n, Just 'Y', n+1),(n, Just 'Z', n+1)], nfaFinal = [n+1]}, n+2)
compile (Seq r1 r2) n = (NFA { nfaStart = n, nfaTransitions = ((getNFATransitions(fst(compile r1 n))) ++  getNFATransitions(fst(compile r2 n))), nfaFinal = getFinalStates(fst(compile r2 n))}, n+2)
compile (Or r1 r2) n = (NFA { nfaStart = n, nfaTransitions =  [(n, Nothing , getFirstofTriplet((head ( getNFATransitions (fst(compile r1 n))))))] ++ [(n, Nothing , getFirstofTriplet((head ( getNFATransitions (fst(compile r2 n))))))] ++ ((getNFATransitions(fst(compile r1 n))) ++  getNFATransitions(fst(compile r2 n))), nfaFinal =[n+1] }, n+2)
compile (Star r) n = (NFA { nfaStart = n, nfaTransitions = (getNFATransitions(fst(compile r n))) ++ [((getLastofTriplet((last ( getNFATransitions (fst(compile r n)))))), Nothing , (getNFAStart(fst(compile r n))))], nfaFinal = [n+1] }, n+2)


getFirstofTriplet :: (a,b,c) -> a
getFirstofTriplet (a,_,_) = a

getLastofTriplet :: (a,b,c) -> a
getLastofTriplet (_,_,c) = c


compile' :: RegEx -> NFA
compile' = fst . flip compile 0
