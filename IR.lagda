%if False
\begin{code}
module IR where

open import Vec public
open import Normal public
open import IxCon public
\end{code}
%endif

Recall that |Fin n| is an enumeration of |n| elements. We might
consider how to take these enumerations as the atomic components of a
dependent type system, closed under $\Sigma$- and $\Pi$-types. Finite
sums and products of finite things are finite, so we can compute their
sizes.

%format sum = "\F{sum}"
%format prod = "\F{prod}"
\begin{code}
sum prod : (n : Nat) -> (Fin n -> Nat) -> Nat
sum   zero     _  = 0
sum   (suc n)  f  = f zero +Nat sum n (f o suc)
prod  zero     _  = 1
prod  (suc n)  f  = f zero *Nat sum n (f o suc)
\end{code}

But can we write down a precise datatype ofthe type expressions in our
finitary system?

%format FTy = "\D{FTy}"
%format fin = "\C{fin}"
\begin{spec}
data FTy : Set where
  fin    : Nat -> FTy
  sg pi  : (S : FTy)(T : Fin ? -> FTy) -> FTy
\end{spec}

I was not quite able to finish the definition, because I could not give the
domain of |T|. Intutively, when we take sums or products over a domain, we
should have one summand or factor for each element of that domain. But we have
only |S|, the expressions which \emph{stands for} the domain. We know that it
is bound to be finite, so I have filled in |Fin ?|, but to make further progress,
we need to know the \emph{size} of |S|. Intuitively, it is easy to compute the
size of an |FTy|: the base case is direct; the structural cases are captured
by |sum| and |prod|. The trouble is that we cannot wait until after dclaring
|FTy| to define the size, because we need size information, right there at that
|?|. What can we do?

%format # = "\F{\#}"
One thing that Agda lets us do is just the thing we need. We can define
|FTy| and its size function, |#|, \emph{simultaneously}.

\begin{code}
mutual

  data FTy : Set where
    fin    : Nat -> FTy
    sg pi  : (S : FTy)(T : Fin (# S) -> FTy) -> FTy

  # : FTy -> Nat
  # (fin n)   = n
  # (sg S T)  = sum   (# S) \ s -> # (T s)
  # (pi S T)  = prod  (# S) \ s -> # (T s)
\end{code}

For example, if we define the forgetful map from |Fin| back to |Nat|,
%format fog = "\F{fog}"
\begin{code}
fog : forall {n} -> Fin n -> Nat
fog zero     = zero
fog (suc i)  = suc (fog i)
\end{code}
we can\nudge{in honour of Gauss} check that
\[
  |# (sg (fin 101) \ s -> fin (fog s)) = 5050|
\]

We have just seen our first example of
\emph{induction-recursion}. Where an inductive definition tells us how
to perform construction of data incrementally, induction-recursion
tells us how to perform construction-\emph{with-interpretation}
incrementally. Together, |(FTy , #) : Fam Nat|, with the interpretation
just telling us sizes, so that |Fin o #| gives an unstructured representation
of a given |FTy| type. If we wanted a structured representation, we
could just as well have interpreted |FTy| in |Set|.

%format FTy' = FTy
%format FEl = "\F{FEl}"
\begin{code}
mutual

  data FTy' : Set where
    fin    : Nat -> FTy'
    sg pi  : (S : FTy')(T : FEl S -> FTy') -> FTy'

  FEl : FTy' -> Set
  FEl (fin n)   = Fin n
  FEl (sg S T)  = Sg  (FEl S) \ s -> FEl (T s)
  FEl (pi S T)  = (s : FEl S) -> FEl (T s)
\end{code}

Now, what has happened? We have |(FTy' , FEl) : Fam Set|, picking out a
subset of |Set| by choosing names for them in |FTy|. But |FTy| is small
enough to be a |Set| itself! IR is the Incredible Ray that shrinks large
sets to small encodings of subsets of them.

Here is a standard example of induction recursion for you to try.
%format FRESHLIST = "\F{FRESHLIST}"
%format FreshList = "\D{FreshList}"
\begin{exe}[|FreshList|]
By means of a suitable choice of recursive interpretation, fill the |?|
with a condition which ensures that |FreshList|s have \emph{distinct}
elements. Try to make sure that, for any concrete |FreshList|, |ok|
can be inferred trivially.
\begin{spec}
module FRESHLIST (X : Set)(Xeq? : (x x' : X) -> Dec (x == x')) where
  mutual
    data FreshList : Set where
      []   : FreshList
      _,_  : (x : X)(xs : FreshList){ok : ?} -> FreshList
\end{spec}
%if False
\begin{code}
module FRESHLIST (X : Set)(Xeq? : (x x' : X) -> Dec (x == x')) where
  mutual
    data FreshList : Set where
      []   : FreshList
      _,_  : (x : X)(xs : FreshList){ok : Fresh x xs} -> FreshList
    Fresh : X -> FreshList -> Set
    Fresh x [] = One
    Fresh x (x' , xs) with Xeq? x x'
    ... | (tt , _) = Zero
    ... | (ff , _) = Fresh x xs
\end{code}
%endif
\end{exe}

\section{Records}

Randy Pollack identified the task of modelling \emph{record} types as a
key early use of induction-recursion, motivated to organise libraries for
mathematical structure.

It doesn't take IR to have a go at modelling records, just something a
bit like |Desc|, but just describing the right-nested |Sg|-types.

%format RecR = "\D{RecR}"
%format !>RR = !> "_{\!\F{RR}}"
%format <!_!>RR = <! _ !>RR
\begin{code}
data RecR : Set1 where
  <>   : RecR
  _,_  : (A : Set)(R : A -> RecR) -> RecR

<!_!>RR : RecR -> Set
<! <> !>RR     = One
<! A , R !>RR  = Sg A \ a -> <! R a !>RR
\end{code}

That gives us a very flexible, variant notion of record, where the
values of earlier fields can determine the entire structure of the rest
of the record. Sometimes, however, it may be too flexible: you cannot
tell from a |RecR| description how many fields a record has---indeed, this
quantity may vary from record to record. You can, of course, count the fields
in an actual record, then define projection. You do it.

\begin{exe}[projection from |RecR|]
Show how to compute the size of a record, then define the projections,
first of types, then of values.
%format sizeRR = "\F{sizeRR}"
%format TyRR = "\F{TyRR}"
%format vaRR = "\F{vaRR}"
\begin{spec}
sizeRR : (R : RecR) -> <! R !>RR -> Nat
sizeRR R r = ?

TyRR : (R : RecR)(r : <! R !>RR) -> Fin (sizeRR R r) -> Set
TyRR R r i = ?

vaRR : (R : RecR)(r : <! R !>RR)(i : Fin (sizeRR R r)) -> TyRR R r i
vaRR R r i = ?
\end{spec}
%if False
\begin{code}
sizeRR : (R : RecR) -> <! R !>RR -> Nat
sizeRR <>       _        = zero
sizeRR (A , R)  (a , r)  = suc (sizeRR (R a) r)

TyRR : (R : RecR)(r : <! R !>RR) -> Fin (sizeRR R r) -> Set
TyRR <>       _        ()
TyRR (A , R)  (a , r)  zero     = A
TyRR (A , R)  (a , r)  (suc i)  = TyRR (R a) r i

vaRR : (R : RecR)(r : <! R !>RR)(i : Fin (sizeRR R r)) -> TyRR R r i
vaRR <>       _        ()
vaRR (A , R)  (a , r)  zero     = a
vaRR (A , R)  (a , r)  (suc i)  = vaRR (R a) r i
\end{code}
%endif
\end{exe}

Of course, we could enforce uniformity of length by indexing.
But a bigger problem with |RecR| is that, being right-nested, our access
to it is left-anchored. Extending a record with more fields whose types
depend on existing fields (e.g., adding laws to a record of operations)
is a difficult right-end access, as is suffix-truncation.

Sometimes we want to know that we are writing down a signature with a
fixed set of fields, and we want easy extensibility at the dependent
right end. That means \emph{left}-nested record types (also known as
\emph{contexts}). And that's where we need IR.

%format RecL = "\D{RecL}"
%format !>RL = !> "_{\!\F{RL}}"
%format <!_!>RL = <! _ !>RL
\begin{code}
mutual

  data RecL : Set1 where
    Em : RecL
    _::_ : {n : Nat}(R : RecL)(A : <! R !>RL -> Set)  -> RecL

  <!_!>RL : RecL -> Set
  <! Em !>RL      = One
  <! R :: A !>RL  = Sg <! R !>RL A
\end{code}

\begin{exe}[projection from |RecL|]
%format sizeRL = "\F{sizeRL}"
%format TyRL = "\F{TyRL}"
%format vaRL = "\F{vaRL}"
Show how to compute the size of a |RecL| without knowing the
individual record. Show how to interpret a projection as a
function from a record, first for types, then values.
\begin{spec}
sizeRL : RecL -> Nat
sizeRL R = ?

TyRL : (R : RecL) -> Fin (sizeRL R) -> <! R !>RL -> Set
TyRL R i = ?

vaRL : (R : RecL)(i : Fin (sizeRL R))(r : <! R !>RL) -> TyRL R i r
vaRL R i = ?
\end{spec}
%if False
\begin{code}
sizeRL : RecL -> Nat
sizeRL Em = zero
sizeRL (R :: A) = suc (sizeRL R)

TyRL : (R : RecL) -> Fin (sizeRL R) -> <! R !>RL -> Set
TyRL Em ()
TyRL (R :: A) zero = A o fst
TyRL (R :: A) (suc i) = TyRL R i o fst

vaRL : (R : RecL)(i : Fin (sizeRL R))(r : <! R !>RL) -> TyRL R i r
vaRL Em ()
vaRL (R :: A) zero = snd
vaRL (R :: A) (suc i) = vaRL R i o fst
\end{code}
%endif
\end{exe}

\begin{exe}[truncation]
Show how to truncate a record signature from a given field and compute the
corresponding projection on structures.
%format TruncRL = "\F{TruncRL}"
%format truncRL = "\F{truncRL}"
\begin{spec}
TruncRL : (R : RecL) -> Fin (sizeRL R) -> RecL
TruncRL R i = ?

truncRL : (R : RecL)(i : Fin (sizeRL R)) -> <! R !>RL -> <! TruncRL R i !>RL
truncRL R i = ?
\end{spec}
%if False
\begin{code}
TruncRL : (R : RecL) -> Fin (sizeRL R) -> RecL
TruncRL Em ()
TruncRL (R :: A) zero = R
TruncRL (R :: A) (suc i) = TruncRL R i

truncRL : (R : RecL)(i : Fin (sizeRL R)) -> <! R !>RL -> <! TruncRL R i !>RL
truncRL Em ()
truncRL (R :: A) zero = fst
truncRL (R :: A) (suc i) = truncRL R i o fst
\end{code}
%endif
\end{exe}


\subsection{Manifest Fields}

Pollack extends his notion of record with \emph{manifest fields}, i.e., fields
whose values are computed from earlier fields. It is rather like allowing
\emph{definitions} in contexts.

First, I define the type of data with a manifest value (sometimes also known
as \emph{singletons}). I deliberately keep the index right of the colon to
force Agda to store the singleton value in the data structure.
%format Manifest = "\D{Manifest}"
\nudge{Why is |Manifest| not an Agda record?}
\begin{code}
data Manifest {A : Set} : A -> Set where
  <$_$> : (a : A) -> Manifest a
\end{code}

%if False
\begin{code}
mproj : forall {A}{a : A} -> Manifest a -> A
mproj <$ a $> = a
\end{code}
%endif

Now, I extend the notion of record signature with a constructor for manifest
fields. I could have chosen simply to omit these fields from the record
structure, but instead I make them |Manifest| so that projection need not
involve recomputation. I also index by size, to save on measuring.
%format RecM = "\D{RecM}"
%format !>RM = !> "_{\!\F{RM}}"
%format <!_!>RM = <! _ !>RM
%format :<: = ::
%format :>: = "\C{\ni}"
%format _:<:_:>:_ = _ :<: _ :>: _
\begin{code}
mutual

  data RecM : Nat -> Set1 where
    Em         : RecM zero
    _::_       : {n : Nat}(R : RecM n)  (A : <! R !>RM -> Set) -> RecM (suc n)
    _:<:_:>:_  : {n : Nat}(R : RecM n)  (A : <! R !>RM -> Set)
                                        (a : (r : <! R !>RM) -> A r) -> RecM (suc n)

  <!_!>RM : {n : Nat} -> RecM n -> Set
  <! Em !>RM             = One
  <! R :: A !>RM         = Sg <! R !>RM A
  <! R :<: A :>: a !>RM  = Sg <! R !>RM (Manifest o a)
\end{code}

\begin{exe}[projection from |RecM|]
%format sizeRM = "\F{sizeRM}"
%format TyRM = "\F{TyRM}"
%format vaRM = "\F{vaRM}"
Implement projection for |RecM|.
\begin{spec}
TyRM : {n : Nat}(R : RecM n) -> Fin n -> <! R !>RM -> Set
TyRM R i = ?

vaRM : {n : Nat}(R : RecM n)(i : Fin n)(r : <! R !>RM) -> TyRM R i r
vaRM R i = ?
\end{spec}
Be careful not to recompute the value of a manifest field.
%if False
\begin{code}
TyRM : {n : Nat}(R : RecM n) -> Fin n -> <! R !>RM -> Set
TyRM Em ()
TyRM (R :: A) zero = A o fst
TyRM (R :: A) (suc i) = TyRM R i o fst
TyRM (R :<: A :>: _) zero = A o fst
TyRM (R :<: A :>: _) (suc i) = TyRM R i o fst

vaRM : {n : Nat}(R : RecM n)(i : Fin n)(r : <! R !>RM) -> TyRM R i r
vaRM Em () _
vaRM (R :: A) zero (r , a) = a
vaRM (R :: A) (suc i) (r , a) = vaRM R i r
vaRM (R :<: A :>: a) zero (r , m) = mproj m
vaRM (R :<: A :>: _) (suc i) (r , _)= vaRM R i r
\end{code}
%endif
\end{exe}


\begin{exe}[record extension]
%format REx = "\D{REx}"
%format rfog = "\F{rfog}"
When building libraries of structures, we are often concerned with the idea
of one record signature being the extension of another. The following
\begin{spec}
mutual

  data REx : {n m : Nat} -> RecM n -> RecM m -> Set1 where
    Em : REx Em Em

  rfog :  forall {n m}{R : RecM n}{R' : RecM m}(X : REx R R') ->
          <! R' !>RM -> <! R !>RM
  rfog Em <> = <>
\end{spec}
describes evidence |REx R R'| that |R'| is an extension of |R|, interpreted by
|rfog| as a map from |<! R' !>RM| back to |<! R !>RM|. Unfortunately, it captures
only the fact that the empty record extends itself.
Extend |REx| to allow retention of every field, insertion of new fields,
and conversion of abstract to manifest fields.
%if False
\begin{code}
mutual

  data REx : {n m : Nat} -> RecM n -> RecM m -> Set1 where
    Em : REx Em Em
    keep :  forall {n m}{R : RecM n}{R' : RecM m}(X : REx R R') ->
            {A : <! R !>RM -> Set} -> REx (R :: A) (R' :: (A o rfog X))
    keepM :  forall {n m}{R : RecM n}{R' : RecM m}(X : REx R R') ->
             {A : <! R !>RM -> Set} ->
             {a : (r : <! R !>RM) -> A r} ->
             REx (R :<: A :>: a) (R' :<: (A o rfog X) :>: (a o rfog X))
    manif :  forall {n m}{R : RecM n}{R' : RecM m}(X : REx R R') ->
             {A : <! R !>RM -> Set} ->
             (a : (r' : <! R' !>RM) -> A (rfog X r')) ->
             REx (R :: A) (R' :<: (A o rfog X) :>: a)
    new :  forall {n m}{R : RecM n}{R' : RecM m}(X : REx R R') ->
           (A : <! R' !>RM -> Set) -> REx R (R' :: A)
    newM :  forall {n m}{R : RecM n}{R' : RecM m}(X : REx R R') ->
            (A : <! R' !>RM -> Set) ->
            (a : (r' : <! R' !>RM) -> A r') ->
            REx R (R' :<: A :>: a)

  rfog :  forall {n m}{R : RecM n}{R' : RecM m}(X : REx R R') ->
          <! R' !>RM -> <! R !>RM
  rfog Em <> = <>
  rfog (keep X) (r' , a) = rfog X r' , a
  rfog (keepM X) (r' , m) = rfog X r' , m
  rfog (manif X a) (r' , m) = rfog X r' , mproj m
  rfog (new X A) (r' , a) = rfog X r'
  rfog (newM X A a) (r' , m) = rfog X r'
\end{code}
%endif
(For my solution, I attempted to show that I could always construct
the identity extension. Thus far, I have been defeated by equational
reasoning in an overly intensional setting.)
\end{exe}


\section{A Universe}

We've already seen that we can use IR to build a little internal
universe. I have a favourite such universe, with a scattering of
base types, dependent pairs and functions, and Petersson-Synek trees.
That's quite a lot of |Set|, right there!

%format TU = "\D{TU}"
%format redp = "^{\C{\prime}}"
%format Zero' = "\C{Zero}" redp
%format One' = "\C{One}" redp
%format Two' = "\C{Two}" redp
%format Sg' = "\C{\Upsigma}" redp
%format Pi' = "\C{\Uppi}" redp
%format Tree' = "\C{Tree}" redp
%format !>TU = !> "_{\!\F{TU}}"
%format <!_!>TU = <! _ !>TU
\begin{code}
mutual
  data TU : Set where
    Zero' One' Two' : TU
    Sg' Pi' : (S : TU)(T : <! S !>TU -> TU) -> TU
    Tree' :  (I : TU)
             (F :  <! I  !>TU  -> Sg TU \ S ->
                   <! S  !>TU  -> Sg TU \ P ->
                   <! P  !>TU  -> <! I !>TU  )
             (i : <! I !>TU) -> TU

  <!_!>TU : TU -> Set
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
\end{code}

The |TU| universe is not closed under a principle of inductive-recursive
definition, so the shrinking ray has not shrunk the shrinking raygun.

\begin{exe}[|TU| examples]
Check that you can encode natural numbers, lists and vectors in |TU|.
For an encore, try the simply typed $\lambda$-calculus.
\end{exe}


\section{Universe Upon Universe}

Not only can you build one small universe inside |Set| using
induction-recursion, you can build a \emph{predicative hierarchy}
of them. The key is to define the `next universe' operator, and then
iterate it. The following construction takes a universe |X| and 
builds another, |NU X|, on top.
%format NU = "\D{NU}"
%format U' = "\C{U}" redp
%format El' = "\C{El}" redp
%format Nat' = "\C{Nat}" redp
%format !>NU = !> "_{\!\F{NU}}"
%format <!_!>NU = <! _ !>NU
\begin{code}
mutual

  data NU (X : Fam Set) : Set where
    U' : NU X
    El' : fst X -> NU X
    Nat' : NU X
    Pi' : (S : NU X)(T : <! S !>NU -> NU X) -> NU X

  <!_!>NU : forall {X} -> NU X -> Set
  <!_!>NU {U , El}  U'       = U
  <!_!>NU {U , El}  (El' T)  = El T
  <! Nat'     !>NU           = Nat
  <! Pi' S T  !>NU           = (s : <! S !>NU) -> <! T s !>NU
\end{code}
As you can see, |NU X| has names |El' T| for the types in |X| and a
name |U'| for |X| itself. Now we can jack up universes as far as we like.

%format EMPTY = "\F{EMPTY}"
%format LEVEL = "\F{LEVEL}"
\begin{code}
EMPTY : Fam Set
EMPTY = Zero , \ ()

LEVEL : Nat -> Fam Set
LEVEL zero     = NU EMPTY , <!_!>NU
LEVEL (suc n)  = NU (LEVEL n) , <!_!>NU
\end{code}

This hierarchy is explicitly cumulative: |El'| embeds types
upward without changing their meaning. One consequence is that we have
a redundancy of representation:
\begin{exe}[|Nat -> Nat|]
Find five names for |Nat -> Nat| in |fst (LEVEL 1)|.
%if False
\begin{code}
infixr 4 _,_
nat2nat : List (fst (LEVEL 1))
nat2nat
  =  (Pi' Nat' \ _ -> Nat')
  ,  (Pi' (El' Nat') \ _ -> Nat')
  ,  (Pi' Nat' \ _ -> El' Nat')
  ,  (Pi' (El' Nat') \ _ -> El' Nat')
  ,  El' (Pi' Nat' \ _ -> Nat')
  ,  <>
\end{code}
%endif
\end{exe}


\subsection{A Redundancy-Free Hierarchy}

We can try to eliminate the redundancy by including only the names
for lower universes at each level: we do not need to embed |Nat -> Nat|
from |LEVEL 0|, because |LEVEL 1| has a perfectly good version.
This time, we parametrize the universe by a de Bruijn indexed collection
of the previous universes.
%format HU = "\D{HU}"
%format HPREDS = "\F{HPREDS}"
%format HSET = "\F{HSET}"
%format !>HU = !> "_{\!\F{HU}}"
%format <!_!>HU = <! _ !>HU
\begin{code}
mutual

  data HU {n}(U : Fin n -> Set) : Set where
    U'    : Fin n -> HU U
    Nat'  : HU U
    Pi'   : (S : HU U)(T : <! S !>HU -> HU U) -> HU U

  <!_!>HU : forall {n}{U : Fin n -> Set} -> HU U -> Set
  <!_!>HU {U = U} (U' i)  = U i
  <! Nat'     !>HU        = Nat
  <! Pi' S T  !>HU        = (s : <! S !>HU) -> <! T s !>HU
\end{code}

To finish the job, we must build the collections of levels to hand to
|HU|. At each step, level |zero| is the new top level, built with a fresh
appeal to |HU|, but lower levels can be projected from the previous
collection.
\begin{code}
HPREDS : (n : Nat) -> Fin n -> Set
HPREDS zero     ()
HPREDS (suc n)  zero     = HU (HPREDS n)
HPREDS (suc n)  (suc i)  = HPREDS n i

HSET : Nat -> Set
HSET n = HU (HPREDS n)
\end{code}
Note that |HSET n| is indeed |<! U' zero !>HU| at level |suc n|.

The trouble with this representation, however, is that it is not
cumulative for free. Intuitively, every type at each level has a counterpart
at all higher levels, but how can we get our hands on it?

\begin{exe}[fool's errand]
Find out what breaks when you try to implement cumulativity.
What equation do you need to hold? Can you prove it?
%format Cumu = "\F{Cumu}"
\begin{spec}
Cumu : (n : Nat)(T : HSET n) -> HSET (suc n)
Cumu n T = ?
\end{spec}
%if False
\begin{spec}
mutual
  Cumu : (n : Nat)(T : HSET n) -> HSET (suc n)
  Cumu n (U' i) = U' (suc i)
  Cumu n Nat' = Nat'
  Cumu n (Pi' S T)
    = Pi' (Cumu n S) \ s -> Cumu n (T (subst (Cumuq n S) id s))

  Cumuq : (n : Nat)(T : HSET n) -> <! Cumu n T !>HU == <! T !>HU
  Cumuq n (U' i)     = refl
  Cumuq n Nat'       = refl
  Cumuq n (Pi' S T)  with Cumu n S | Cumuq n S
  Cumuq n (Pi' S T)  | S' | q with <! S' !>HU 
  Cumuq n (Pi' S T) | S' | refl | .(<! S !>HU) = {!!}
\end{spec}
%endif
\end{exe}


\section{Encoding Induction-Recursion}

So far, we have been making |mutual| declarations of inductive types
and recursive functions to which Agda has said `yes'. Clearly, however,
we could write down some rather paradoxical definitions if we were not
careful. Fortunately, the following is not permitted,
%format VV = "\mbox{\brownBG{\ensuremath{\D{VV}}}}"
%format V' = "\C{V}" redp
%format !>VV = !> "_{\!\F{VV}}"
%format <!_!>VV = <! _ !>VV
\begin{spec}
mutual -- rejected

  data VV : Set where
    V' : VV
    Pi' : (S : VV)(T : <! S !>VV -> VV) -> VV

  <!_!>VV : VV -> Set
  <! V' !>VV       = VV
  <! Pi' S T !>VV  = (s : <! S !>VV) -> <! T s !>VV
\end{spec}
but it was not always so.

It would perhaps help to make sense of what is possible, as well as to provide
some sort of metaprogramming facility, to give an encoding of the permitted
inductive-recursive definitions. Such a thing was given by Peter Dybjer and
Anton Setzer in 1999. Their encoding is (morally) as follows,
describing one node of an inductive recursive type rather in the manner
of a right-nested record, but one from which we expect to read off a |J|-value,
and whose children allow us to read off |I|-values.
%format DS = "\D{DS}"
%format io = "\C{\upiota}"
%format de = "\C{\updelta}"
\begin{code}
data DS (I J : Set1) : Set1 where
  io  : J -> DS I J                                   -- no more fields
  sg  : (S : Set)(T : S         -> DS I J) -> DS I J  -- ordinary field
  de  : (H : Set)(T : (H -> I)  -> DS I J) -> DS I J  -- child field
\end{code}
We interpret a |DS I J| as a functor from |Fam I| to |Fam J|: I build the
components separately for readability.
%format !>DS = !> "_{\!\F{DS}}"
%format <!_!>DS = <! _ !>DS
\begin{code}
<!_!>DS : forall {I J} -> DS I J -> Fam I -> Fam J
<! io j    !>DS  Xxi
  =  One
  ,  \ { <>        -> j }
<! sg S T  !>DS  Xxi
  =  (Sg S \ s -> fst (<! T s !>DS Xxi))
  ,  \ { (s , t)   -> snd (<! T s !>DS Xxi) t }
<! de H T  !>DS  (X , xi)
  =  (Sg (H -> X) \ hx -> fst (<! T (xi o hx) !>DS (X , xi)))
  ,  \ { (hx , t)  -> snd (<! T (xi o hx) !>DS (X , xi)) t }
\end{code}
In each case, we must say which set is being encoded and how to read off
a |J| from a value in that set. The |iota| constructor carries exactly the
|j| required. The other two specify a field in the node structure, from
which the computation of the |J| gains some information. The |sg| specifies
a field of type |S|, and the rest of the structure may depend on a value
of type |S|.

The |de| case is the clever bit. It specifies a place for an
|H|-indexed bunch of children, and even though we do not fix what set
represents the children, we do know that they allow us to read off an
|I|. Correspondingly, the rest of the structure can at least depend on
knowing a function in |H -> I| which gives access to the interpretation
of the children. Once we plug in a specific |(X , xi) : Fam I|, we
represent the field by the \emph{small} function space |hx : H -> X|,
then the composition |xi o hx| tells us how to compute the
\emph{large} meaning of each child.

%format idDS = "\F{idDS}"
\begin{exe}[|idDS|]
A morphism from |(X , xi)| to |(Y , yi)| in |Fam I| is a function |f : X -> Y|
such that |xi = yi o f|.
Construct a code for the identity functor on |Fam I|, being
\begin{spec}
idDS : {I : Set1} -> DS I I
idDS = ?
\end{spec}
such that
\[
  |<! idDS !>DS| \cong |id|
\]
in the sense that both take isomorphic inputs to isomorphic outputs.
%if False
\begin{code}
idDS : forall {I} -> DS I I
idDS = de One \ f -> io (f <>)
\end{code}
%endif
\end{exe}

With this apparatus in place, we could now tie the recursive knot\ldots
%format DataDS = "\D{DataDS}"
%format !>Da = !> "_{\!\F{Da}}"
%format <!_!>Da = <! _ !>Da
\begin{spec}
mutual  -- fails positivity check and termination check

  data DataDS {I}(D : DS I I) : Set where
    <$_$> : fst (<! D !>DS (DataDS D , <!_!>Da)) -> DataDS D

  <!_!>Da : {I : Set1}{D : DS I I} -> DataDS D -> I
  <!_!>Da {D = D} <$ ds $> = snd (<! D !>DS (DataDS D , <!_!>Da)) ds
\end{spec}
\ldots{}if only the positivity checker could trace the construction of
the node set through the tupled presentation of |<!_!>DS| and the
termination checker could accept that the recursive
invocation of |<!_!>DS| is used only for the children packed up inside
the node record. Not for the first or the last time, we can only get out of the jam
by inlining the interpretation:
%format NoDS = "\F{NoDS}"
%format DeNoDS = "\F{DeNoDS}"
\begin{code}
mutual

  data DataDS {I}(D : DS I I) : Set where
    <$_$> : NoDS D D -> DataDS D

  <!_!>Da : {I : Set1}{D : DS I I} -> DataDS D -> I
  <!_!>Da {D = D} <$ ds $> = DeNoDS D D ds

  NoDS : {I : Set1}(D D' : DS I I) -> Set
  NoDS D (io i)    = One
  NoDS D (sg S T)  = Sg S \ s ->                 NoDS D (T s)
  NoDS D (de H T)  = Sg (H -> DataDS D) \ hd ->  NoDS D (T (\ h -> <! hd h !>Da))

  DeNoDS : {I : Set1}(D D' : DS I I) -> NoDS D D' -> I
  DeNoDS D (io i)    <>        = i
  DeNoDS D (sg S T)  (s , t)   = DeNoDS D (T s) t
  DeNoDS D (de H T)  (hd , t)  = DeNoDS D (T (\ h -> <! hd h !>Da)) t
\end{code}

\begin{exe}[encode |TU|]
Construct an encoding of |TU| in |DS Set Set|.
\end{exe}

There is one current snag with the |DS I J| coding of functors yielding
inductive-recursive definitions, as you will discover if you attempt the
following exercise.

%format coDS = "\F{coDS}"
\begin{exe}[composition for |DS|]
This is an open problem. Construct
\begin{spec}
coDS : forall {I J K} -> DS J K -> DS I K -> DS I K
coDS E D = ?
\end{spec}
such that
\[
  |<! coDS E D !>DS| \cong |<! E !>DS o <! D !>DS|
\]
Alternatively, find a counterexample which wallops the very possibility of
|coDS|.
\end{exe}

In the next section, we can try to do something about the problem.


\section{Irish Induction-Recursion}
