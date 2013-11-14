module Hello where

-- Oh, you made it! Well done! This line is a comment.

-- In the beginning, Agda knows nothing, but we can teach it about numbers.

data Nat : Set where
  zero  :  Nat
  suc   :  Nat -> Nat

-- Now we can say how to add numbers.

_+_ : Nat -> Nat -> Nat
zero + n = n
suc m + n = suc (m + n)

-- Now we can try adding some numbers.

four : Nat
four = (suc (suc zero)) + (suc (suc zero))

-- To make it go, select "Evaluate term to normal form" from the
-- Agda menu, then type "four", without the quotes, and press return.

-- Hopefully, you should get a response
--   suc (suc (suc (suc zero)))

