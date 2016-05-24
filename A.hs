
module A where

data Digit =
    Zero
  | One
  | Two
  | Three
  | Four
  | Five
  | Six
  | Seven
  | Eight
  | Nine
  deriving (Show,Eq)

sucD :: Digit -> (Digit,Digit)
sucD Zero   = (Zero,One)
sucD One    = (Zero,Two)
sucD Two    = (Zero,Three)
sucD Three  = (Zero,Four)
sucD Four   = (Zero,Five)
sucD Five   = (Zero,Six)
sucD Six    = (Zero,Seven)
sucD Seven  = (Zero,Eight)
sucD Eight  = (Zero,Nine)
sucD Nine   = (One,Zero)

suc :: (Digit,Digit) -> (Digit,Digit)
suc (d,u) = let (carry,u') = sucD u
            in if carry == Zero
               then (d,u')
               else let (carry',d') = sucD d
                    in if carry' == Zero
                       then (d',u')
                       else (Zero,Zero)

