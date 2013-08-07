%if False
\begin{code}
module IxCon where

open import Vec public
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

