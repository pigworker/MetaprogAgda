module Exe6 where

open import IR public

mutual

  EQ : (X Y : TU) -> TU * (<! X !>TU -> <! Y !>TU -> TU)

  _<->_ : TU -> TU -> TU
  X <-> Y = fst (EQ X Y)

  Eq : (X : TU)(x : <! X !>TU) -> (Y : TU)(y : <! Y !>TU) -> TU
  Eq X x Y y = snd (EQ X Y) x y

  EQ  Zero'  Zero'  = One' , \ _ _ -> One'
  EQ  One'   One'   = One' , \ _ _ -> One'
  EQ  Two'   Two'   = One' , \
    {  tt  tt  -> One'
    ;  ff  ff  -> One'
    ;  _   _   -> Zero'
    }

  EQ (Sg' S T) (Sg' S' T')
    =  (  Sg' (S <-> S') \ _ ->
          Pi' S \ s -> Pi' S' \ s' -> Pi' (Eq S s S' s') \ _ ->
          T s <-> T' s'  )
    ,  \ {  (s , t) (s' , t') ->
            Sg' (Eq S s S' s') \ _ -> Eq (T s) t (T' s') t' }

  EQ (Pi' S T) (Pi' S' T')
    =  (  Sg' (S' <-> S) \ _ ->
          Pi' S' \ s' -> Pi' S \ s -> Pi' (Eq S' s' S s) \ _ ->
          T s <-> T' s'  )
    ,  \ {  f f' ->
            Pi' S \ s -> Pi' S' \ s' -> Pi' (Eq S s S' s') \ _ ->
            Eq (T s) (f s) (T' s') (f' s') }

  EQ (Tree' I F i) (Tree' I' F' i')
    =  (  Sg' (I <-> I') \ _ -> Sg' (Eq I i I' i') \ _ ->
          Pi' I \ i -> Pi' I' \ i' -> Pi' (Eq I i I' i') \ _ ->
          let  (S , K) = F i ; S' , K' = F' i'
          in   Sg' (S <-> S') \ _ ->
               Pi' S \ s -> Pi' S' \ s' -> Pi' (Eq S s S' s') \ _ ->
               let (P , r) = K s ; (P' , r') = K' s' 
               in  Sg' (P' <-> P) \ _ ->
                   Pi' P' \ p' -> Pi' P  \ p -> Pi' (Eq P' p' P p) \ _ ->
                   Eq I (r p) I' (r' p') )
    ,  teq i i' where
       teq : (i : <! I !>TU) -> (i' : <! I' !>TU) ->
             <! Tree' I F i !>TU -> <! Tree' I' F' i' !>TU -> TU
       teq i i' <$ s , k $> <$ s' , k' $>
         =  let  (S , K) = F i  ; (S' , K') = F' i'
                 (P , r) = K s  ; (P' , r') = K' s'
            in   Sg' (Eq S s S' s') \ _ ->
                 Pi' P \ p -> Pi' P' \ p' -> Pi' (Eq P p P' p') \ _ ->
                 teq (r p) (r' p') (k p) (k' p')

  EQ _ _ = Zero' , \ _ _ -> One'

{- {exe}[define |coe|, postulate |coh|]
Implement |coe|rcion, assuming |coh|erence. -}

coe : (X Y : TU) -> <! X <-> Y !>TU -> <! X !>TU -> <! Y !>TU

postulate
  coh : (X Y : TU)(Q : <! X <-> Y !>TU)(x : <! X !>TU) -> <! Eq X x Y (coe X Y Q x) !>TU

coe X Y Q x = {!!}

{- {exe}[explore failing to prove |reflTU|]
Try proving -}

reflTU : (X : TU)(x : <! X !>TU) -> <! Eq X x X x !>TU
reflTU X x = {!!}


------------------------------------------------------------------------
data Sort : Set where set prop : Sort

IsSet : Sort -> Set
IsSet set   = One
IsSet prop  = Zero

mutual
  data PU (u : Sort) : Set where
    Zero' One' : PU u
    Two'   :  {_ : IsSet u} -> PU u
    Sg'    :  (S : PU u)(T : <! S !>PU -> PU u) -> PU u
    Pi'    :  (S : PU set)(T : <! S !>PU -> PU u) -> PU u
    Tree'  :  {_ : IsSet u}
              (I : PU set)
              (F :  <! I  !>PU  -> Sg (PU set) \ S ->
                    <! S  !>PU  -> Sg (PU set) \ P ->
                    <! P  !>PU  -> <! I !>PU  )
              (i : <! I !>PU) -> PU u
    Prf'   :  {_ : IsSet u} -> PU prop -> PU u

  <!_!>PU : forall {u} -> PU u -> Set
  <! Zero'        !>PU  = Zero
  <! One'         !>PU  = One
  <! Two'         !>PU  = Two
  <! Sg' S T      !>PU  = Sg <! S !>PU \ s -> <! T s !>PU
  <! Pi' S T      !>PU  = (s : <! S !>PU) -> <! T s !>PU
  <! Tree' I F i  !>PU  = ITree
    (   (\ i -> <! fst (F i) !>PU)
    <i  (\ i s -> <! fst (snd (F i) s) !>PU)
    $   (\ i s p -> snd (snd (F i) s) p)
    )   i
  <! Prf' P       !>PU  = <! P !>PU

{- {exe}[observational propositional equality]
Reconstruct the definition of observational equality in this more refined
setting. Take equality of propositions to be mutual implication and
equality of proofs to be trivial: after all, equality for proofs of the
atomic |Zero'| and |One'| propositions are trivial. -}

_/\_ : PU prop -> PU prop -> PU prop
P /\ Q = Sg' P \ _ -> Q

_=>_ : PU prop -> PU prop -> PU prop
P => Q = Pi' (Prf' P) \ _ -> Q

mutual

  PEQ : (X Y : PU set) -> PU prop * (<! X !>PU -> <! Y !>PU -> PU prop)

  _<=>_ : PU set -> PU set -> PU prop
  X <=> Y = fst (PEQ X Y)

  PEq : (X : PU set)(x : <! X !>PU) -> (Y : PU set)(y : <! Y !>PU) -> PU prop
  PEq X x Y y = snd (PEQ X Y) x y

  PEQ  (Prf' P) (Prf' Q) = ((P => Q) /\ (Q => P)) , \ _ _ -> One'
  -- \orange{more code goes here}
  PEQ  _ _ = Zero' , \ _ _ -> One'
