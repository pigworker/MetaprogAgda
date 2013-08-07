%if False
\begin{code}
module IxCon where

open import Vec public
open import STLC public
\end{code}
%endif

There are lots of ways to present indexed containers, giving ample
opportunities for exercises, but I shall use the Hancock presentation,
as it has become my preferred version, too.

The idea is to describe functors between indexed families of sets.
%format i> = "\D{\triangleright}"
%format _i>_ = "\us{" i> "}"
%format ri = "\F{ri}"
%format _<1_$_ = _ <1 _ $ _
%format !>i = !> "_{\F{i}}"
%format <!_!>i = <! _ !>i
\begin{code}
record _i>_ (I J : Set) : Set1 where
  constructor _<1_$_
  field
    Sh : J        -> Set
    Po : (j : J)  -> Sh j -> Set
    ri : (j : J)(s : Sh j)(p : Po j s) -> I
  <!_!>i : (I -> Set) -> (J -> Set)
  <!_!>i X j = Sg (Sh j) \ s -> (p : Po j s) -> X (ri j s p)
open _i>_ public
\end{code}
An |I i> J| describes a |J|-indexed thing with places for |I|-indexed elements.
Correspondingly, some |j : J| tells us which sort of thing we're making,
determining a shape set |Sh j| and a position family |Po j|, just as with plain
containers. The |ri| function then determines which |I|-index is demanded in
each element position.

\paragraph{Interaction structures} Hancock calls these indexed
containers \emph{interaction structures}. Consider |J| to be the set
of possible `states of the world' before an interaction, and |I| the
possible states afterward.  The `before' states will determine a
choice of commands we can issue, each of which has a set of possible
responses which will then determine the state `after'. An interaction
structure thus describes the predicate transformer which describes the
precondition for achieving a postcondition by one step of interaction.
We are just using proof-relevant Hoare logic as the type system!


\section{Petersson-Synek Trees}

Kent Petersson and Dan Synek proposed a universal inductive family,
amounting to the fixpoint of an indexed container

\begin{code}
data Tree {J : Set}(C : J i> J)(j : J) : Set where
  <$_$> : <! C !>i (Tree C) j -> Tree C j
\end{code}

The natural numbers are a friendly, if degenerate example.
%format NatC = "\F{NatC}"
%format zeroC = "\F{zeroC}"
%format sucC = "\F{sucC}"
\begin{code}
NatC : One i> One
NatC = (\ _ -> Two) <1 (\ _ -> Zero <?> One) $ _

zeroC : Tree NatC <>
zeroC = <$ tt , magic $>

sucC : Tree NatC <> -> Tree NatC <>
sucC n = <$ ff , pure n $>
\end{code}
This is just the indexed version of the |W|-type, so the same issue with
extensionality arises.

We may also define the node structure for vectors as an instance.
%format VecC = "\F{VecC}"
%format VS = "\F{VS}"
%format VP = "\F{VP}"
%format Vr = "\F{Vr}"
\begin{code}
VecC : Set -> Nat i> Nat
VecC X = VS <1 VP $ Vr where  -- depending on the length
  VS : Nat -> Set
  VS zero             = One   -- nil is unlabelled
  VS (suc n)          = X     -- cons carried an element
  VP : (n : Nat) -> VS n -> Set
  VP zero     _       = Zero  -- nil has no children
  VP (suc n)  _       = One   -- cons has one child
  Vr : (n : Nat)(s : VS n)(p : VP n s) -> Nat
  Vr zero     <>  ()          -- nil has no children to index
  Vr (suc n)  x   <>  = n     -- the tail of a cons has the length one less
\end{code}
