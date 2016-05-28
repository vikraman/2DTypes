{-# OPTIONS_GHC -Wall #-}
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
ceq Id (Seq Test Test) = True
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

data Dir = Forward | Back
  deriving (Eq,Show)

isFinal :: State -> Bool
isFinal (Exit _ _ Empty) = True
isFinal _ = False

unload :: State -> Value
unload (Exit _ v Empty) = v
unload _ = error "Not final state"

traceForward :: State -> a -> a
traceForward s@(Enter _ _ _) = trace (">>> " ++ show s ++ "\n\n")
traceForward _ = id

traceBack :: State -> a -> a
traceBack s@(Exit _ _ _) = trace ("<<< " ++ show s ++ "\n\n")
traceBack _ = id

eval :: State -> Value
eval = loopForward
  where loopForward s = traceForward s $
          let (d,s') = stepForward s
          in if isFinal s'
             then unload s'
             else if d == Forward
                  then loopForward s'
                  else trace ("****************** BACK *******************\n\n") $ loopBack s'
        loopBack s = traceBack s $
          let (d,s') = stepBack s
          in if d == Back
             then loopBack s'
             else trace ("******************* FORWARD *******************\n\n") $ loopForward s'

stepForward :: State -> (Dir,State)
stepForward (Exit c1 v (Fst k c2)) = (Forward, Enter c2 v (Snd c1 k))
stepForward (Exit c2 v (Snd c1 k)) = (Forward, Exit (Seq c1 c2) v k)
stepForward (Exit c1 v (LeftPlus k c2)) = (Forward, Exit (Plus c1 c2) (Inj1 v) k)
stepForward (Exit c2 v (RightPlus c1 k)) = (Forward, Exit (Plus c1 c2) (Inj2 v) k)
stepForward (Exit c1 v1 (LeftTimes k c2 v2)) = (Forward, Enter c2 v2 (RightTimes c1 v1 k))
stepForward (Exit c2 v2 (RightTimes c1 v1 k)) = (Forward, Exit (Times c1 c2) (Pair v1 v2) k)
stepForward (Enter Zeroe (Inj2 v) k) = (Forward, Exit Zeroe v k)
stepForward (Enter Zeroi v k) = (Forward, Exit Zeroi (Inj2 v) k)
stepForward (Enter SwapPlus (Inj1 v1) k) = (Forward, Exit SwapPlus (Inj2 v1) k)
stepForward (Enter SwapPlus (Inj2 v2) k) = (Forward, Exit SwapPlus (Inj1 v2) k)
stepForward (Enter AssoclPlus (Inj1 v1) k) = (Forward, Exit AssoclPlus (Inj1 (Inj1 v1)) k)
stepForward (Enter AssoclPlus (Inj2 (Inj1 v2)) k) = (Forward, Exit AssoclPlus (Inj1 (Inj2 v2)) k)
stepForward (Enter AssoclPlus (Inj2 (Inj2 v3)) k) = (Forward, Exit AssoclPlus (Inj2 v3) k)
stepForward (Enter AssocrPlus (Inj1 (Inj1 v1)) k) = (Forward, Exit AssocrPlus (Inj1 v1) k)
stepForward (Enter AssocrPlus (Inj1 (Inj2 v2)) k) = (Forward, Exit AssocrPlus (Inj2 (Inj1 v2)) k)
stepForward (Enter AssocrPlus (Inj2 v3) k) = (Forward, Exit AssocrPlus (Inj2 (Inj2 v3)) k)
stepForward (Enter Unite (Pair Unit v) k) = (Forward, Exit Unite v k)
stepForward (Enter Uniti v k) = (Forward, Exit Uniti (Pair Unit v) k)
stepForward (Enter SwapTimes (Pair v1 v2) k) = (Forward, Exit SwapTimes (Pair v2 v1) k)
stepForward (Enter AssoclTimes (Pair v1 (Pair v2 v3)) k) = (Forward, Exit AssoclTimes (Pair (Pair v1 v2) v3) k)
stepForward (Enter AssocrTimes (Pair (Pair v1 v2) v3) k) = (Forward, Exit AssocrTimes (Pair v1 (Pair v2 v3)) k)
stepForward (Enter Distrib (Pair (Inj1 v1) v3) k) = (Forward, Exit Distrib (Inj1 (Pair v1 v3)) k)
stepForward (Enter Distrib (Pair (Inj2 v2) v3) k) = (Forward, Exit Distrib (Inj2 (Pair v2 v3)) k)
stepForward (Enter Factor (Inj1 (Pair v1 v3)) k) = (Forward, Exit Factor (Pair (Inj1 v1) v3) k)
stepForward (Enter Distrib (Inj2 (Pair v2 v3)) k) = (Forward, Exit Factor (Pair (Inj2 v2) v3) k)
stepForward (Enter Id v k) = (Forward, Exit Id v k)
stepForward (Enter (Seq c1 c2) v k) = (Forward, Enter c1 v (Fst k c2))
stepForward (Enter (Plus c1 c2) (Inj1 v) k) = (Forward, Enter c1 v (LeftPlus k c2))
stepForward (Enter (Plus c1 c2) (Inj2 v) k) = (Forward, Enter c2 v (RightPlus c1 k))
stepForward (Enter (Times c1 c2) (Pair v1 v2) k) = (Forward, Enter c1 v1 (LeftTimes k c2 v2))
stepForward (Enter (Eta p) Unit k) = (Forward, Exit (Eta p) (Pair (Comb p) (Recip p)) k)
stepForward (Enter (Epsilon r) (Pair (Recip q) (Comb p)) k) | ceq p q = (Forward, Exit (Epsilon r) Unit k)
                                                            | otherwise =
  (Back, Enter (Epsilon r) (Pair (Recip q) (Comb p)) k)
-- these cases were previously missing
stepForward (Enter DistribZero (Pair _ _) _) = 
  error "impossible case (DistribZero), but Haskell can't see that"
stepForward (Enter FactorZero _ _) = 
  error "impossible case (FactorZero), but Haskell can't see that"
stepForward (Enter (Sym c) v k) = stepBack (Exit c v k)
stepForward (Enter Test _ _) = error "should never evaluate Test"
stepForward (Exit _ _ Empty) = error "should not be trying to step at end"
-- these cases would all be eliminated by dependent types
-- these were added by hand after checking that the proper case was in place
stepForward (Enter Zeroe _ _) = error "ill-typed"
stepForward (Enter SwapPlus _ _) = error "ill-typed"
stepForward (Enter AssoclPlus _ _) = error "ill-typed"
stepForward (Enter AssocrPlus _ _) = error "ill-typed"
stepForward (Enter Unite _ _) = error "ill-typed"
stepForward (Enter SwapTimes _ _) = error "ill-typed"
stepForward (Enter AssoclTimes _ _) = error "ill-typed"
stepForward (Enter AssocrTimes _ _) = error "ill-typed"
stepForward (Enter Factor _ _) = error "ill-typed"
stepForward (Enter Distrib _ _) = error "ill-typed"
stepForward (Enter (Plus _ _) _ _) = error "ill-typed"
stepForward (Enter (Times _ _) _ _) = error "ill-typed"
stepForward (Enter (Eta _) _ _) = error "ill-typed"
stepForward (Enter (Epsilon _) _ _) = error "ill-typed"
stepForward (Enter DistribZero _ _) = error "ill-typed"

stepBack :: State -> (Dir,State)
stepBack (Enter c1 v (Fst k c2)) = (Back, Enter (Seq c1 c2) v k)
stepBack (Enter c2 v (Snd c1 k)) = (Back, Exit c1 v (Fst k c2))
stepBack (Enter c1 v (LeftPlus k c2)) = (Back, Enter (Plus c1 c2) (Inj1 v) k)
stepBack (Enter c2 v (RightPlus c1 k)) = (Back, Enter (Plus c1 c2) (Inj2 v) k)
stepBack (Enter c1 v1 (LeftTimes k c2 v2)) = (Back, Enter (Times c1 c2) (Pair v1 v2) k)
stepBack (Enter c2 v2 (RightTimes c1 v1 k)) = (Back, Exit c1 v1 (LeftTimes k c2 v2))
stepBack (Exit Zeroe v k) = (Back, Enter Zeroe (Inj2 v) k)
stepBack (Exit Zeroi (Inj2 v) k) = (Back, Enter Zeroi v k)
stepBack (Exit SwapPlus (Inj2 v1) k) = (Back, Enter SwapPlus (Inj1 v1) k)
stepBack (Exit SwapPlus (Inj1 v2) k) = (Back, Enter SwapPlus (Inj2 v2) k)
stepBack (Exit AssoclPlus (Inj1 (Inj1 v1)) k) = (Back, Enter AssoclPlus (Inj1 v1) k)
stepBack (Exit AssoclPlus (Inj1 (Inj2 v2)) k) = (Back, Enter AssoclPlus (Inj2 (Inj1 v2)) k)
stepBack (Exit AssoclPlus (Inj2 v3) k) = (Back, Enter AssoclPlus (Inj2 (Inj2 v3)) k)
stepBack (Exit AssocrPlus (Inj1 v1) k) = (Back, Enter AssocrPlus (Inj1 (Inj1 v1)) k)
stepBack (Exit AssocrPlus (Inj2 (Inj1 v2)) k) = (Back, Enter AssocrPlus (Inj1 (Inj2 v2)) k)
stepBack (Exit AssocrPlus (Inj2 (Inj2 v3)) k) = (Back, Enter AssocrPlus (Inj2 v3) k)
stepBack (Exit Unite v k) = (Back, Enter Unite (Pair Unit v) k)
stepBack (Exit Uniti (Pair Unit v) k) = (Back, Enter Uniti v k)
stepBack (Exit SwapTimes (Pair v2 v1) k) = (Back, Enter SwapTimes (Pair v1 v2) k)
stepBack (Exit AssoclTimes (Pair (Pair v1 v2) v3) k) = (Back, Enter AssoclTimes (Pair v1 (Pair v2 v3)) k)
stepBack (Exit AssocrTimes (Pair v1 (Pair v2 v3)) k) = (Back, Enter AssocrTimes (Pair (Pair v1 v2) v3) k)
stepBack (Exit Distrib (Inj1 (Pair v1 v3)) k) = (Back, Enter Distrib (Pair (Inj1 v1) v3) k)
stepBack (Exit Distrib (Inj2 (Pair v2 v3)) k) = (Back, Enter Distrib (Pair (Inj2 v2) v3) k)
stepBack (Exit Factor (Pair (Inj1 v1) v3) k) = (Back, Enter Factor (Inj1 (Pair v1 v3)) k)
stepBack (Exit Factor (Pair (Inj2 v2) v3) k) = (Back, Enter Distrib (Inj2 (Pair v2 v3)) k)
stepBack (Exit Id v k) = (Back, Enter Id v k)
stepBack (Exit (Seq c1 c2) v k) = (Back, Exit c2 v (Snd c1 k))
stepBack (Exit (Plus c1 c2) (Inj1 v) k) = (Back, Exit c1 v (LeftPlus k c2))
stepBack (Exit (Plus c1 c2) (Inj2 v) k) = (Back, Exit c2 v (RightPlus c1 k))
stepBack (Exit (Times c1 c2) (Pair v1 v2) k) = (Back, Exit c2 v2 (RightTimes c1 v1 k))
stepBack (Exit (Eta r) (Pair (Comb p) (Recip q)) k) | ceq p q = 
  (Forward, Exit (Eta r) (Pair (Comb (Seq r p)) (Recip (Seq r q))) k)
                                                    | otherwise =
  error "Unexpected eta back if we are starting from left"
stepBack (Exit (Epsilon _) Unit _) =
  error "Unexpected epsilon back if we are starting from left"
stepBack (Exit DistribZero (Pair _ _) _) = 
  error "impossible case (DistribZero), but Haskell can't see that"
stepBack (Exit FactorZero _ _) = 
  error "impossible case (FactorZero), but Haskell can't see that"
stepBack (Exit (Sym c) v k) = stepForward (Enter c v k)
stepBack (Exit Test _ _) = error "should never evaluate Test"
stepBack (Enter _ _ Empty) = error "should not be trying to step back at start"
stepBack (Exit Zeroi _ _) = error "ill-typed"
stepBack (Exit Uniti _ _) = error "ill-typed"
stepBack (Exit SwapPlus _ _) = error "ill-typed"
stepBack (Exit AssoclPlus _ _) = error "ill-typed"
stepBack (Exit AssocrPlus _ _) = error "ill-typed"
stepBack (Exit SwapTimes _ _) = error "ill-typed"
stepBack (Exit AssoclTimes _ _) = error "ill-typed"
stepBack (Exit AssocrTimes _ _) = error "ill-typed"
stepBack (Exit Factor _ _) = error "ill-typed"
stepBack (Exit Distrib _ _) = error "ill-typed"
stepBack (Exit (Plus _ _) _ _) = error "ill-typed"
stepBack (Exit (Times _ _) _ _) = error "ill-typed"
stepBack (Exit (Eta _) _ _) = error "ill-typed"
stepBack (Exit (Epsilon _) _ _) = error "ill-typed"
stepBack (Exit DistribZero _ _) = error "ill-typed"

-- Credit Card Example

ex :: Combinator
ex = foldr1 Seq [Uniti, Times (Eta Test) Id, AssocrTimes, Times Id (Epsilon Test), SwapTimes, Unite]

load :: Combinator -> Value -> State
load c v = Enter c v Empty

test1, test2 :: Value
test1 = eval $ load ex (Comb Test)
test2 = eval $ load ex (Comb Id)

