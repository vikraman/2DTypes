module AM where

import Debug.Trace

-- Abstract Machine for PI/

data Combinator = Zeroe | Zeroi
                | SwapPlus 
                | AssoclPlus | AssocrPlus
                | Unite | Uniti
                | SwapTimes 
                | AssoclTimes | AssocrTimes
                | DistribZero | FactorZero
                | Distrib | Factor
                | Id | Sym Combinator | Seq Combinator Combinator
                | Plus Combinator Combinator | Times Combinator Combinator
                | Eta Combinator | Epsilon Combinator
                | Test
  deriving (Eq,Show)

ceq :: Combinator -> Combinator -> Bool
ceq (Seq Test Test) Id = True
ceq c1 c2 = c1 == c2

data Value = Unit | Inj1 Value | Inj2 Value | Pair Value Value
           | Comb Combinator | Recip Combinator
  deriving (Eq,Show)

data Context = Empty
             | Fst Context Combinator | Snd Combinator Context
             | LeftTimes Context Combinator Value | RightTimes Combinator Value Context
             | LeftPlus Context Combinator | RightPlus Combinator Context
  deriving (Eq,Show)

data State = Enter Combinator Value Context | Exit Combinator Value Context
  deriving (Eq,Show)

isFinal :: State -> Bool
isFinal (Exit c v Empty) = True
isFinal _ = False

evalForward :: State -> State
evalForward s = loop s
  where loop s = trace (">>" ++ show s ++ "\n\n") $
                 let s' = stepForward s
                 in if isFinal s'
                    then s'
                    else loop s'

evalBack :: State -> State
evalBack s = loop s
  where loop s = trace ("<<" ++ show s ++ "\n\n") $
                 loop (stepBack s)

stepForward :: State -> State
stepForward (Enter (Seq c1 c2) v k) = Enter c1 v (Fst k c2)
stepForward (Enter (Plus c1 c2) (Inj1 v) k) = Enter c1 v (LeftPlus k c2)
stepForward (Enter (Plus c1 c2) (Inj2 v) k) = Enter c2 v (RightPlus c1 k)
stepForward (Enter (Times c1 c2) (Pair v1 v2) k) = Enter c1 v1 (LeftTimes k c2 v2)
stepForward (Enter Zeroe (Inj2 v) k) = Exit Zeroe v k
stepForward (Enter Zeroi v k) = Exit Zeroi (Inj2 v) k
stepForward (Enter SwapPlus (Inj1 v1) k) = Exit SwapPlus (Inj2 v1) k
stepForward (Enter SwapPlus (Inj2 v2) k) = Exit SwapPlus (Inj1 v2) k
stepForward (Enter AssoclPlus (Inj1 v1) k) = Exit AssoclPlus (Inj1 (Inj1 v1)) k
stepForward (Enter AssoclPlus (Inj2 (Inj1 v2)) k) = Exit AssoclPlus (Inj1 (Inj2 v2)) k
stepForward (Enter AssoclPlus (Inj2 (Inj2 v3)) k) = Exit AssoclPlus (Inj2 v3) k
stepForward (Enter AssocrPlus (Inj1 (Inj1 v1)) k) = Exit AssocrPlus (Inj1 v1) k
stepForward (Enter AssocrPlus (Inj1 (Inj2 v2)) k) = Exit AssocrPlus (Inj2 (Inj1 v2)) k
stepForward (Enter AssocrPlus (Inj2 v3) k) = Exit AssocrPlus (Inj2 (Inj2 v3)) k
stepForward (Enter Unite (Pair Unit v) k) = Exit Unite v k
stepForward (Enter Uniti v k) = Exit Uniti (Pair Unit v) k
stepForward (Enter SwapTimes (Pair v1 v2) k) = Exit SwapTimes (Pair v2 v1) k
stepForward (Enter AssoclTimes (Pair v1 (Pair v2 v3)) k) = Exit AssoclTimes (Pair (Pair v1 v2) v3) k
stepForward (Enter AssocrTimes (Pair (Pair v1 v2) v3) k) = Exit AssocrTimes (Pair v1 (Pair v2 v3)) k
stepForward (Enter Distrib (Pair (Inj1 v1) v3) k) = Exit Distrib (Inj1 (Pair v1 v3)) k
stepForward (Enter Distrib (Pair (Inj2 v2) v3) k) = Exit Distrib (Inj2 (Pair v2 v3)) k
stepForward (Enter Factor (Inj1 (Pair v1 v3)) k) = Exit Factor (Pair (Inj1 v1) v3) k
stepForward (Enter Distrib (Inj2 (Pair v2 v3)) k) = Exit Factor (Pair (Inj2 v2) v3) k
stepForward (Enter Id v k) = Exit Id v k
stepForward (Exit c1 v (Fst k c2)) = Enter c2 v (Snd c1 k)
stepForward (Exit c2 v (Snd c1 k)) = Exit (Seq c1 c2) v k
stepForward (Exit c1 v (LeftPlus k c2)) = Exit (Plus c1 c2) (Inj1 v) k
stepForward (Exit c2 v (RightPlus c1 k)) = Exit (Plus c1 c2) (Inj2 v) k
stepForward (Exit c1 v1 (LeftTimes k c2 v2)) = Enter c2 v2 (RightTimes c1 v1 k)
stepForward (Exit c2 v2 (RightTimes c1 v1 k)) = Exit (Times c1 c2) (Pair v1 v2) k
stepForward (Enter (Eta p) Unit k) = Exit (Eta p) (Pair (Comb p) (Recip p)) k
stepForward (Enter (Epsilon r) (Pair (Recip q) (Comb p)) k) | ceq p q = Exit (Epsilon r) Unit k
                                                            | otherwise =
  evalBack (Enter (Epsilon r) (Pair (Recip q) (Comb p)) k)

stepBack :: State -> State
stepBack (Enter c1 v (Fst k c2)) = (Enter (Seq c1 c2) v k)
stepBack (Enter c1 v (LeftPlus k c2)) = (Enter (Plus c1 c2) (Inj1 v) k)
stepBack (Enter c2 v (RightPlus c1 k)) = (Enter (Plus c1 c2) (Inj2 v) k)
stepBack (Enter c1 v1 (LeftTimes k c2 v2)) = (Enter (Times c1 c2) (Pair v1 v2) k)
stepBack (Exit Zeroe v k) = (Enter Zeroe (Inj2 v) k)
stepBack (Exit Zeroi (Inj2 v) k) = (Enter Zeroi v k)
stepBack (Exit SwapPlus (Inj2 v1) k) = (Enter SwapPlus (Inj1 v1) k)
stepBack (Exit SwapPlus (Inj1 v2) k) = (Enter SwapPlus (Inj2 v2) k)
stepBack (Exit AssoclPlus (Inj1 (Inj1 v1)) k) = (Enter AssoclPlus (Inj1 v1) k)
stepBack (Exit AssoclPlus (Inj1 (Inj2 v2)) k) = (Enter AssoclPlus (Inj2 (Inj1 v2)) k)
stepBack (Exit AssoclPlus (Inj2 v3) k) = (Enter AssoclPlus (Inj2 (Inj2 v3)) k)
stepBack (Exit AssocrPlus (Inj1 v1) k) = (Enter AssocrPlus (Inj1 (Inj1 v1)) k)
stepBack (Exit AssocrPlus (Inj2 (Inj1 v2)) k) = (Enter AssocrPlus (Inj1 (Inj2 v2)) k)
stepBack (Exit AssocrPlus (Inj2 (Inj2 v3)) k) = (Enter AssocrPlus (Inj2 v3) k)
stepBack (Exit Unite v k) = (Enter Unite (Pair Unit v) k)
stepBack (Exit Uniti (Pair Unit v) k) = (Enter Uniti v k)
stepBack (Exit SwapTimes (Pair v2 v1) k) = (Enter SwapTimes (Pair v1 v2) k)
stepBack (Exit AssoclTimes (Pair (Pair v1 v2) v3) k) = (Enter AssoclTimes (Pair v1 (Pair v2 v3)) k)
stepBack (Exit AssocrTimes (Pair v1 (Pair v2 v3)) k) = (Enter AssocrTimes (Pair (Pair v1 v2) v3) k)
stepBack (Exit Distrib (Inj1 (Pair v1 v3)) k) = (Enter Distrib (Pair (Inj1 v1) v3) k)
stepBack (Exit Distrib (Inj2 (Pair v2 v3)) k) = (Enter Distrib (Pair (Inj2 v2) v3) k)
stepBack (Exit Factor (Pair (Inj1 v1) v3) k) = (Enter Factor (Inj1 (Pair v1 v3)) k)
stepBack (Exit Factor (Pair (Inj2 v2) v3) k) = (Enter Distrib (Inj2 (Pair v2 v3)) k)
stepBack (Exit Id v k) = (Enter Id v k)
stepBack (Enter c2 v (Snd c1 k)) = (Exit c1 v (Fst k c2))
stepBack (Exit (Seq c1 c2) v k) = (Exit c2 v (Snd c1 k))
stepBack (Exit (Plus c1 c2) (Inj1 v) k) = (Exit c1 v (LeftPlus k c2))
stepBack (Exit (Plus c1 c2) (Inj2 v) k) = (Exit c2 v (RightPlus c1 k))
stepBack (Enter c2 v2 (RightTimes c1 v1 k)) = (Exit c1 v1 (LeftTimes k c2 v2))
stepBack (Exit (Times c1 c2) (Pair v1 v2) k) = (Exit c2 v2 (RightTimes c1 v1 k))
stepBack (Exit (Eta r) (Pair (Comb p) (Recip q)) k) | ceq p q = Enter (Eta r) Unit k
                                                    | otherwise =
  evalForward (Exit (Eta r) (Pair (Comb (Seq r p)) (Recip q)) k)
stepBack (Exit (Epsilon p) Unit k) = (Enter (Epsilon p) (Pair (Recip p) (Comb p)) k)

-- Credit Card Example

ex :: Combinator
ex = foldr1 Seq [Uniti, Times (Eta Test) Id, AssocrTimes, Times Id (Epsilon Test), SwapTimes, Unite]

load :: Combinator -> Value -> State
load c v = Enter c v Empty

unload :: State -> Value
unload (Exit c v Empty) = v
unload _ = error "Not final state"

test1 = unload $ evalForward $ load ex (Comb Test)
test2 = unload $ evalForward $ load ex (Comb Id)

