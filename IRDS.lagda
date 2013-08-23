%if False
\begin{code}
module IRDS where

open import Vec public
open import Normal public
open import IxCon public
\end{code}
%endif


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
%format !>ds = !> "_{\!\F{ds}}"
%format <!_!>ds = <! _ !>ds
\begin{spec}
mutual  -- fails positivity check and termination check

  data DataDS {I}(D : DS I I) : Set where
    <$_$> : fst (<! D !>DS (DataDS D , <!_!>ds)) -> DataDS D

  <!_!>ds : {I : Set1}{D : DS I I} -> DataDS D -> I
  <!_!>ds {D = D} <$ ds $> = snd (<! D !>DS (DataDS D , <!_!>ds)) ds
\end{spec}
\ldots{}if only the positivity checker could trace the construction of
the node set through the tupled presentation of |<!_!>DS| and the
termination checker could accept that the recursive
invocation of |<!_!>DS| is used only for the children packed up inside
the node record. Not for the first or the last time, we can only get out of the jam
by inlining the interpretation:
%format NoDS = "\F{NoDS}"
%format DeDS = "\F{DeDS}"
\begin{code}
mutual

  data DataDS {I}(D : DS I I) : Set where
    <$_$> : NoDS D D -> DataDS D

  <!_!>ds : {I : Set1}{D : DS I I} -> DataDS D -> I
  <!_!>ds {D = D} <$ ds $> = DeDS D D ds

  NoDS : {I : Set1}(D D' : DS I I) -> Set
  NoDS D (io i)    = One
  NoDS D (sg S T)  = Sg S \ s ->                 NoDS D (T s)
  NoDS D (de H T)  = Sg (H -> DataDS D) \ hd ->  NoDS D (T (\ h -> <! hd h !>ds))

  DeDS : {I : Set1}(D D' : DS I I) -> NoDS D D' -> I
  DeDS D (io i)    <>        = i
  DeDS D (sg S T)  (s , t)   = DeDS D (T s) t
  DeDS D (de H T)  (hd , t)  = DeDS D (T (\ h -> <! hd h !>ds)) t
\end{code}

\begin{exe}[encode |TU|]
Construct an encoding of |TU| in |DS Set Set|.
\end{exe}

If you have an eye for this sort of thing, you may have noticed that
|DS I| is a \emph{monad}, with |iota| as its `return'.

%format bindDS = "\F{bindDS}"
\begin{exe}[|bindDS| and its meaning]
Implement the appropriate |bindDS| operator, corresponding to substitution
at |iota|.
\begin{spec}
bindDS : forall {I J K} -> DS I J -> (J -> DS I K) -> DS I K
bindDS T U = ?
\end{spec}
%if False
\begin{code}
bindDS : forall {I J K} -> DS I J -> (J -> DS I K) -> DS I K
bindDS (io j) U = U j
bindDS (sg S T) U = sg S \ s -> bindDS (T s) U
bindDS (de H T) U = de H \ f -> bindDS (T f) U
\end{code}
%endif
Show that |bindDS| corresponds to a kind of |Sg| by implementing
pairing and projections:
%format pairDS = "\F{pairDS}"
%format projDS = "\F{projDS}"
\begin{spec}
pairDS :  forall {I J K}(T : DS I J)(U : J -> DS I K){X : Fam I} ->
          (t : fst (<! T !>DS X))(u : fst (<! U (snd (<! T !>DS X) t) !>DS X))
          -> fst (<! bindDS T U !>DS X)
pairDS T U t u = ?

projDS :  forall {I J K}(T : DS I J)(U : J -> DS I K){X : Fam I} ->
          fst (<! bindDS T U !>DS X) ->
          Sg (fst (<! T !>DS X)) \ t -> fst (<! U (snd (<! T !>DS X) t) !>DS X)
projDS T U tu = ?
\end{spec}
%if False
\begin{code}
pairDS :  forall {I J K}(T : DS I J)(U : J -> DS I K){X : Fam I} ->
          (t : fst (<! T !>DS X))(u : fst (<! U (snd (<! T !>DS X) t) !>DS X))
          -> fst (<! bindDS T U !>DS X)
pairDS (io j) U <> u = u
pairDS (sg S T) U (s , t) u = s , pairDS (T s) U t u
pairDS (de H T) U {_ , d} (f , t) u = f , pairDS (T (d o f)) U t u

projDS :  forall {I J K}(T : DS I J)(U : J -> DS I K){X : Fam I} ->
          fst (<! bindDS T U !>DS X) ->
          Sg (fst (<! T !>DS X)) \ t -> fst (<! U (snd (<! T !>DS X) t) !>DS X)
projDS (io j) U u = <> , u
projDS (sg S T) U (s , tu) with projDS (T s) U tu
... | t , u = (s , t) , u
projDS (de H T) U {_ , d} (f , tu) with projDS (T (d o f)) U tu
... | t , u = (f , t) , u
\end{code}
%endif
Which coherence properties hold?
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

