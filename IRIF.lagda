%if False
\begin{code}
module IRIF where

open import IRDS public
\end{code}
%endif

So I went to this meeting with some friends who like containers,
induction-recursion, and other interesting animals in the zoo of
datatypes. I presented what I thought was just a boring |Desc|-like
rearrangement of Dybjer and Setzer's encoding of induction-recursion.
`That's not IR!' said the audience, and it remains an open problem
whether or not they were correct: it is certainly IR-ish, but we do
not yet know whether it captures just the same class of functors as
Dybjer and Setzer's encoding, or strictly more. (If the latter, we
shall need a new model construction, to ensure the system's
consistency.)

%format ka = "\C{\upkappa}"
%format Irish = "\D{Irish}"
%format Info = "\F{Info}"
I give an inductive-recursive definition of IR. The type
|Irish I| describes node structures where children can be interpreted
in |I|. Deferring the task of interpreting such a node, let us rather
compute the type of |Info|rmation we can learn from it. Note that
|Info {I} T| is large because |I| is, but fear not, for it is not
the type of the nodes themselves.
\begin{code}
mutual

  data Irish (I : Set1) : Set1 where
    io  : Irish I
    ka  : Set -> Irish I
    pi  : (S : Set)(T : S -> Irish I) -> Irish I
    sg  : (S : Irish I)(T : Info S -> Irish I) -> Irish I

  Info : forall {I} -> Irish I -> Set1
  Info {I} io    = I
  Info (ka A)    = Up A
  Info (pi S T)  = (s : S) -> Info (T s)
  Info (sg S T)  = Sg (Info S) \ s -> Info (T s)
\end{code}
To interpret |pi| and |sg|, we shall need to equip |Fam| with
pointwise lifting and dependent pairs, respectively.
%format PiF = "\F{\Uppi F}"
%format SgF = "\F{\Upsigma F}"
\begin{code}
PiF :  (S : Set){J : S -> Set1}(T : (s : S) -> Fam (J s)) ->
       Fam ((s : S) -> J s)
PiF S T  = ((s : S) -> fst (T s)) , \ f s -> snd (T s) (f s)

SgF :  {I : Set1}(S : Fam I){J : I -> Set1}(T : (i : I) -> Fam (J i)) ->
       Fam (Sg I J)
SgF S T  =  Sg (fst S) (fst o (T o snd S))
         ,  \ { (s , t) -> snd S s , snd (T (snd S s)) t }
\end{code}
Now, for any |T : Irish I|, if someone gives us a |Fam I| to represent
children, we can compute a |Fam (Info T)| --- a \emph{small} node structure
from which the large |Info T| can be extracted.
%format Node = "\F{Node}"
\begin{code}
Node : forall {I}(T : Irish I) -> Fam I -> Fam (Info T)
Node io        X  =  X
Node (ka A)    X  =  A , up
Node (pi S T)  X  =  PiF S \ s -> Node (T s) X
Node (sg S T)  X  =  SgF (Node S X) \ iS -> Node (T iS) X
\end{code}

A functor from |Fam I| to |Fam J| is then given by a pair
%format IF = "\F{IF}"
%format !>IF = !> "_{\!\F{IF}}"
%format <!_!>IF = <! _ !>IF
\begin{code}
IF : Set1 -> Set1 -> Set1
IF I J = Sg (Irish I) \ T -> Info T -> J

<!_!>IF : forall {I J} -> IF I J -> Fam I -> Fam J
<! T , d !>IF X = d $F Node T X
\end{code}

With a certain tedious inevitability, we find that Agda rejects the
obvious attempt to tie the knot.
%format DataIF = "\D{DataIF}"
%format !>if = !> "_{\!\F{if}}"
%format <!_!>if = <! _ !>if
\begin{spec}
mutual -- fails positivity and termination checks

  data DataIF {I}(F : IF I I) : Set where
    <$_$> : fst (<! F !>IF (DataIF F , <!_!>if)) -> DataIF F

  <!_!>if : forall {I}{F : IF I I} -> DataIF F -> I
  <!_!>if {F = F} <$ ds $> = snd (<! F !>IF (DataIF F , <!_!>if)) ds
\end{spec}
Again, specialization of |Node| fixes the problem
%format NoIF = "\F{NoIF}"
%format DeIF = "\F{DeIF}"
\begin{code}
mutual

  data DataIF {I}(F : IF I I) : Set where
    <$_$> : NoIF F (fst F) -> DataIF F

  <!_!>if : forall {I}{F : IF I I} -> DataIF F -> I
  <!_!>if {F = F} <$ rs $> = snd F (DeIF F (fst F) rs)

  NoIF : forall {I}(F : IF I I)(T : Irish I) -> Set
  NoIF F io        = DataIF F
  NoIF F (ka A)    = A
  NoIF F (pi S T)  = (s : S) -> NoIF F (T s)
  NoIF F (sg S T)  = Sg (NoIF F S) \ s -> NoIF F (T (DeIF F S s))

  DeIF : forall {I}(F : IF I I)(T : Irish I) -> NoIF F T -> Info T
  DeIF F io        r        = <! r !>if
  DeIF F (ka A)    a        = up a
  DeIF F (pi S T)  f        = \ s -> DeIF F (T s) (f s)
  DeIF F (sg S T)  (s , t)  = let s' = DeIF F S s in s' , DeIF F (T s') t
\end{code}

\nudge{Given that Agda lets us implement Irish IR, one wonders whether
it allows even more.}Irish IR is a little closer to the user
experience of IR in Agda, in that you give separately a description of your
data's node structure and the `algebra' which decodes it.

\begin{exe}[Irish |TU|]
Give a construction for the |TU| universe as a description-decoder pair in
|IF Set Set|.
\end{exe}

We should check that Irish IR allows at least as much as
Dybjer-Setzer.

\begin{exe}
Show how to define
%format DSIF = "\F{DSIF}"
\begin{spec}
DSIF : forall {I J} -> DS I J -> IF I J
DSIF T = ?
\end{spec}
such that
\[
  |<! DSIF T !>DS| \cong |<! T !>IF|
\]
%if False
\begin{code}
DSIF : forall {I J} -> DS I J -> IF I J
DSIF (io j) = ka One , \ _ -> j
DSIF (sg S T)
  =  (sg (ka S) \ s -> fst (DSIF (T (down s))))
  ,  \ { (s , t) -> snd (DSIF (T (down s))) t }
DSIF (de H T)
  =  (sg (pi H \ _ -> io) \ f -> fst (DSIF (T f)))
  ,  \ { (f , t) -> snd (DSIF (T f)) t }
\end{code}
%endif
\end{exe}

We clearly have an identity for Irish IR.
%format idIF = "\F{idIF}"
\begin{code}
idIF : forall {I} -> IF I I
idIF = io , id
\end{code}

Now, |DS I J| had a substitution-for-|io| structure which induced a
notion of \emph{pairing}, because |io| marks `end of record'.
What makes the Irish encoding conductive to composition is that the
|io|-leaves of an |Irish I| mark where the \emph{children} go.

%format subIF = "\F{subIF}"
\begin{exe}[|subIF|]
Construct a substitution operator for |Irish J| with a refinement
of the following type.
\begin{spec}
subIF : forall {I J}(T : Irish J)(F : IF I J) -> Sg (Irish I) ?
subIF T F = ?
\end{spec}
%if False
\begin{code}
subIF : forall {I J}(T : Irish J)(F : IF I J) -> IF I (Info T)
subIF io F = F
subIF (ka A) F = ka A , id
subIF (pi S T) F
  =  (pi S \ s -> fst (subIF (T s) F))
  ,  \ f s -> snd (subIF (T s) F) (f s)
subIF (sg S T) F with subIF S F
... | SF , f  =  (sg SF \ sf -> fst (subIF (T (f sf)) F))
              ,  \ { (sf , tf) -> f sf , snd (subIF (T (f sf)) F) tf }
\end{code}
%endif
Hint: you will find out what you need in the |sg| case.
\end{exe}

%format coIF = "\F{coIF}"
\begin{exe}[|coIF|]
Now define composition for Irish IR functors.
\begin{spec}
coIF : forall {I J K} -> IF J K -> IF I J -> IF I K
coIF G F = ?
\end{spec}
%if False
\begin{code}
coIF : forall {I J K} -> IF J K -> IF I J -> IF I K
coIF (T , d) F with subIF T F
... | TF , f = TF , (d o f)
\end{code}
%endif
\end{exe}

Some of us are inclined to suspect that |IF| does admit more functors
than |DS|, but the exact status of Irish induction-recursion remains
the stuff of future work.
