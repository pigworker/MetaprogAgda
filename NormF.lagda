%if False
\begin{code}
module NormF where

open import Normal public
\end{code}
%endif



\section{Fixpoints of Normal Functors}

The universal first order simple datatype is given by taking the least
fixpoint of a normal functor.

%format Tree = "\D{Tree}"
%format <$ = "\C{\langle}"
%format $> = "\C{\rangle}"
%format <$_$> = <$ _ $>
\begin{code}
data Tree (N : Normal) : Set where
  <$_$> : <! N !>N (Tree N) -> Tree N
\end{code}

We may, for example, define the natural numbers this way:

%format NatT = "\F{NatT}"
%format zeroT = "\F{zeroT}"
%format sucT = "\F{sucT}"
\begin{code}
NatT : Normal
NatT = Two / 0 <?> 1

zeroT : Tree NatT
zeroT = <$ tt , <> $>

sucT : Tree NatT -> Tree NatT
sucT n = <$ ff , n , <> $>
\end{code}

Of course, to prove these are the natural numbers, we need the eliminator
as well as the constructors.

\begin{exe}
Prove the principle of induction for these numbers.
%format NatInd = "\F{NatInd}"
\begin{spec}
NatInd :  forall {l}(P : Tree NatT -> Set l) ->
          P zeroT ->
          ((n : Tree NatT) -> P n -> P (sucT n)) ->
          (n : Tree NatT) -> P n
NatInd P z s n = ?
\end{spec}
%if False
\begin{code}
NatInd :  forall {l}(P : Tree NatT -> Set l) ->
          P zeroT ->
          ((n : Tree NatT) -> P n -> P (sucT n)) ->
          (n : Tree NatT) -> P n
NatInd P z s <$ tt , <> $> = z
NatInd P z s <$ ff , n , <> $> = s n (NatInd P z s n)
\end{code}
%endif
\end{exe}

Indeed, there's a generic induction principle for the whole lot of these types.
First, we need predicate transformer to generate the induction hypothesis.

%format All = "\F{All}"
\begin{code}
All : forall {l X}(P : X -> Set l){n} -> Vec X n -> Set l
All P <>        = One
All P (x , xs)  = P x * All P xs
\end{code}

We then acquire
%format induction = "\F{induction}"
%format hyps = "\F{hyps}"
\begin{code}
induction :  forall (N : Normal){l}(P : Tree N -> Set l) ->
  ((s : Shape N)(ts : Vec (Tree N) (size N s)) -> All P ts -> P <$ s , ts $>) ->
  (t : Tree N) -> P t
induction N P p <$ s , ts $> = p s ts (hyps ts) where
  hyps : forall {n}(ts : Vec (Tree N) n) -> All P ts
  hyps <>        = <>
  hyps (t , ts)  = induction N P p t , hyps ts
\end{code}

\begin{exe}[decidable equality]
%format Dec = "\F{Dec}"
%format Zero = "\D{Zero}"
We say a property is \emph{decided} if we know whether it is true or false,
where falsity is indicated by function to |Zero|, an empty type.
\begin{spec}
Dec : Set -> Set
Dec X = X + (X -> Zero)
\end{spec}
Show that if a normal functor has decidable equality for its shapes,
then its fixpoint also has decidable equality.
%format eq? = "\F{eq?}"
\begin{spec}
  eq? : (N : Normal)(sheq? : (s s' : Shape N) -> Dec (s == s')) ->
        (t t' : Tree N) -> Dec (t == t')
  eq? N sheq? t t' = ?
\end{spec}
%if False
\begin{code}
mutual
  eq? : (N : Normal)(sheq? : (s s' : Shape N) -> Dec (s == s')) ->
        (t t' : Tree N) -> Dec (t == t')
  eq? N sheq? <$ s , ts $> <$ s' , ts' $> with sheq? s s'
  eq? N sheq? <$ s , ts $> <$ .s , ts' $> | tt , refl with eqs? N sheq? ts ts'
  eq? N sheq? <$ s , ts $> <$ .s , .ts $> | tt , refl  | tt , refl = tt , refl
  eq? N sheq? <$ s , ts $> <$ .s , ts' $> | tt , refl  | ff , no = ff , no o inj where
    inj :  forall  {s}{ts ts' : Vec (Tree N) (size N s)} ->
           <$ s , ts $> == <$ s , ts' $> -> ts == ts'
    inj refl = refl
  eq? N sheq? <$ s , xs $> <$ s' , ts' $> | ff , no = ff , no o inj where
    inj :  forall  {s s' : Shape N}
                   {ts : Vec (Tree N) (size N s)}{ts' : Vec (Tree N) (size N s')} ->
           <$ s , ts $> == <$ s' , ts' $> -> s == s'
    inj refl = refl

  eqs? : (N : Normal)(sheq? : (s s' : Shape N) -> Dec (s == s')) ->
         {n : Nat} -> (ts ts' : Vec (Tree N) n) -> Dec (ts == ts')
  eqs? N sheq? <> <> = tt , refl
  eqs? N sheq? (t , ts) (t' , ts') with eq? N sheq? t t' | eqs? N sheq? ts ts'
  eqs? N sheq? (t , ts) (.t , .ts) | tt , refl | tt , refl = tt , refl
  eqs? N sheq? (t , ts) (.t , ts') | tt , refl | ff , no = ff , no o inj where
    inj :  forall  {n X}{t : X}{ts ts' : Vec X n} ->
           _==_ {X = Vec X (suc n)} (t , ts) (t , ts') -> ts == ts'
    inj refl = refl
  eqs? N sheq? (t , ts) (t' , ts') | ff , no | _ = ff , no o inj where
    inj :  forall  {n X}{t t' : X}{ts ts' : Vec X n} ->
           _==_ {X = Vec X (suc n)} (t , ts) (t' , ts') -> t == t'
    inj refl = refl
\end{code}
%endif
\end{exe}
