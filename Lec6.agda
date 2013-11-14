module Lec6 where

open import IxCon public

data Sort : Set where set prop : Sort

mutual
  data TU : Sort -> Set where
    Zero' One' : {s : Sort} -> TU s
    Two' : TU set
    Sg' : {s : Sort}(S : TU s)(T : <! S !>TU -> TU s) -> TU s
    Pi' : {s : Sort}(S : TU set)(T : <! S !>TU -> TU s) -> TU s
    Tree' :  (I : TU set)
             (F :  <! I  !>TU  -> Sg (TU set) \ S ->
                   <! S  !>TU  -> Sg (TU set) \ P ->
                   <! P  !>TU  -> <! I !>TU  )
             (i : <! I !>TU) -> (TU set)
    Prf' : TU prop -> TU set

  <!_!>TU : forall {s} -> TU s -> Set
  <! Zero'        !>TU  = Zero
  <! One'         !>TU  = One
  <! Two'         !>TU  = Two
  <! Sg' S T      !>TU  = Sg <! S !>TU \ s -> <! T s !>TU
  <! Pi' S T      !>TU  = (s : <! S !>TU) -> <! T s !>TU
  <! Tree' I F i  !>TU  = ITree
    (   (\ i -> <! fst (F i) !>TU)
    <i  (\ i s -> <! fst (snd (F i) s) !>TU)
    $   (\ i s p -> snd (snd (F i) s) p)
    )   i
  <! Prf' P !>TU        = <! P !>TU

data Favourite (f : Nat -> Nat) : Set where
  favourite : (\ x -> zero +Nat x) == f -> Favourite f

plusZero : forall x -> x == x +Nat zero
plusZero zero = refl
plusZero (suc x)  = cong suc (plusZero x)

closedFact : (\ x -> zero +Nat x) == (\ x -> x +Nat zero)
closedFact = extensionality _ _ plusZero

myTerm = subst closedFact Favourite (favourite refl)

help : Favourite (λ x → x +Nat 0)
help = favourite closedFact

-- remark on intensional predicates
-- remark on the need for a more type-based computation mechanism

_/\_ : TU prop -> TU prop -> TU prop
P /\ Q = Sg' P \ _ -> Q

_=>_ : TU prop -> TU prop -> TU prop
P => Q = Pi' (Prf' P) \ _ -> Q

mutual

  EQ : (X Y : TU set) -> TU prop * (<! X !>TU -> <! Y !>TU -> TU prop)

  _<->_ : TU set -> TU set -> TU prop
  X <-> Y = fst (EQ X Y)

  Eq : (X : TU set)(x : <! X !>TU) -> (Y : TU set)(y : <! Y !>TU) -> TU prop
  Eq X x Y y = snd (EQ X Y) x y

  EQ Zero' Zero' = One' , \ _ _ -> One'

  EQ One' One' = One' , \ _ _ -> One'
  EQ Two' Two' = One' , (\
    { tt tt -> One'
    ; ff ff -> One'
    ; _ _ -> Zero'
    })
  EQ (Sg' S T) (Sg' S' T')
    =  ((S <-> S') /\ Pi' S \ s -> Pi' S' \ s' -> Eq S s S' s' => (T s <-> T' s'))
    ,  (\ { (s , t) (s' , t') -> Eq S s S' s' /\ Eq (T s) t (T' s') t' })
  EQ (Pi' S T) (Pi' S' T')
    =  ((S' <-> S) /\ Pi' S' \ s' -> Pi' S \ s -> Eq S' s' S s => (T s <-> T' s'))
    ,  (\ f f' -> Pi' S \ s -> Pi' S' \ s' -> Eq S s S' s' =>
                  Eq (T s) (f s) (T' s') (f' s'))
  EQ (Tree' I F i) (Tree' I' F' i')
    = ((I <-> I') /\ (Eq I i I' i' /\
        Pi' I \ i -> Pi' I' \ i' -> Eq I i I' i' =>
        let (S , k) = F i ; (S' , k') = F' i'
        in  (S <-> S') /\  Pi' S \ s -> Pi' S' \ s' -> Eq S s S' s' =>
            let (P , r) = k s ; (P' , r') = k' s'
            in (P' <-> P) /\  Pi' P' \ p' -> Pi' P \ p -> Eq P' p' P p =>
                Eq I (r p) I' (r' p') ))
    , teq i i' where
    teq : (i : <! I !>TU)(i' : <! I' !>TU) -> 
           <! Tree' I F i !>TU -> <! Tree' I' F' i' !>TU -> TU prop
    teq i i' <$ s , k $> <$ s' , k' $>
     = let (S , K) = F i ; (S' , K') = F' i'
           (P , r) = K s ; (P' , r') = K' s'
       in    Eq S s S' s' /\
            Pi' P \ p -> Pi' P' \ p' -> Eq P p P' p' =>
                teq (r p) (r' p') (k p) (k' p')

  EQ _ _ = Zero' , \ _ _ -> One'

coe : (X Y : TU set) -> <! X <-> Y !>TU -> <! X !>TU -> <! Y !>TU

postulate
  coh :  (X Y : TU set)(Q : <! X <-> Y !>TU)(x : <! X !>TU) ->
         <! Eq X x Y (coe X Y Q x) !>TU

coe Zero' Zero' <> x = x
coe Zero' One' () x
coe Zero' Two' () x
coe Zero' (Sg' Y T) () x
coe Zero' (Pi' Y T) () x
coe Zero' (Tree' Y F i) () x
coe Zero' (Prf' Y) () x
coe One' Zero' () x
coe One' One' <> x = x
coe One' Two' () x
coe One' (Sg' Y T) () x
coe One' (Pi' Y T) () x
coe One' (Tree' Y F i) () x
coe One' (Prf' Y) () x
coe Two' Zero' () x
coe Two' One' () x
coe Two' Two' <> x = x
coe Two' (Sg' Y T) () x
coe Two' (Pi' Y T) () x
coe Two' (Tree' Y F i) () x
coe Two' (Prf' Y) () x
coe (Sg' X T) Zero' () x
coe (Sg' X T) One' () x
coe (Sg' X T) Two' () x
coe (Sg' S T) (Sg' S' T') (SQ , TQ) (s , t)
  = let  s' = coe S S' SQ s
         t' = coe (T s) (T' s') (TQ s s' (coh S S' SQ s)) t
    in   s' , t'
coe (Sg' X T) (Pi' Y T₁) () x
coe (Sg' X T) (Tree' Y F i) () x
coe (Sg' X T) (Prf' Y) () x
coe (Pi' X T) Zero' () x
coe (Pi' X T) One' () x
coe (Pi' X T) Two' () x
coe (Pi' X T) (Sg' Y T₁) () x
coe (Pi' S T) (Pi' S' T') (SQ , TQ) f = \ s' ->
  let s = coe S' S SQ s'
      t = f s
  in  coe (T s) (T' s') (TQ s' s (coh S' S SQ s')) t
coe (Pi' X T) (Tree' Y F i) () x
coe (Pi' X T) (Prf' Y) () x
coe (Tree' X F i) Zero' () x
coe (Tree' X F i) One' () x
coe (Tree' X F i) Two' () x
coe (Tree' X F i) (Sg' Y T) () x
coe (Tree' X F i) (Pi' Y T) () x
coe (Tree' I F i) (Tree' I' F' i') (IQ , (iq , FQ)) x = tcoe i i' iq x where
  tcoe : (i : <! I !>TU)(i' : <! I' !>TU)(iq : <! Eq I i I' i' !>TU) ->
         <! Tree' I F i !>TU -> <! Tree' I' F' i' !>TU
  tcoe i i' iq <$ s , k $> = <$ (
    let  (S , K) = F i ; (S' , K') = F' i'
         (SQ , KQ) = FQ i i' iq
         s' = coe S S' SQ s ; sq = coh S S' SQ s
         (P , r) = K s ; (P' , r') = K' s'
         (PQ , rq) = KQ s s' sq
    in   s' , \ p' ->
         let  p = coe P' P PQ p' ; pq = coh P' P PQ p'
         in   tcoe (r p) (r' p') (rq p' p pq) (k p) ) $>
coe (Tree' X F i) (Prf' Y) () x
coe (Prf' X) Zero' () x
coe (Prf' X) One' () x
coe (Prf' X) Two' () x
coe (Prf' X) (Sg' Y T) () x
coe (Prf' X) (Pi' Y T) () x
coe (Prf' X) (Tree' Y F i) () x
coe (Prf' X) (Prf' Y) () x

postulate
  reflTU : (X : TU set)(x : <! X !>TU) -> <! Eq X x X x !>TU
  RespTU : (X : TU set)(P : <! X !>TU -> TU set)(x x' : <! X !>TU) ->
           <! Eq X x X x' !>TU ->
           <! P x <-> P x' !>TU

substTU : (X : TU set)(P : <! X !>TU -> TU set)(x x' : <! X !>TU) ->
          (q : <! Eq X x X x' !>TU) ->
           <! P x !>TU -> <! P x' !>TU
substTU X P x x' q = coe (P x) (P x') (RespTU X P x x' q)


-- in Coq one might try

data Rep : Set -> Set1 where
  Zero' : Rep Zero
  One' : Rep One
  Sg' : forall {S T} -> Rep S -> ((s : S) -> Rep (T s)) -> Rep (Sg S T)
  -- etc

-- PEQ : forall {X Y} -> Rep X -> Rep Y -> Prop * (X -> Y -> Prop
-- PEQ X Y = ?

