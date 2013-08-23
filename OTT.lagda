%if False
\begin{code}
module OTT where

open import IR public

\end{code}
%endif

We cannot have an equality which is both extensional and decidable.
We choose to keep \emph{judgmental} equality decidable, hence it is
inevitably disappointing, but we introduce a \emph{propositional} equality,
allowing us to give evidence for equations on open terms which the computer
is too stupid to see. Correspondingly, we need a |subst|itution mechanism
to transport values from |P s| to |P t| whenever |s == t|. The way |subst|
has worked thus far is to wait at least until |s jeq t| holds judgmentally,
so that |p : P s| implies |p : P t|, allowing |p| to be transmitted as it
stands. (Waiting for the proof of |s == t| to become |refl| means waiting
at least until |s jeq t|.)

The trouble with this way to compute |subst| is that we have no way to
explain its computation if there are provably equal closed terms which
are not judgmentally equal. We can add axioms for extensionality and
retain consistency, even extracting working programs which compile
|subst| to |id| and never compute under a binder. However, such axioms
impede open computation. If we want a propositional equality to make
up for our disappointment with judgmental equality, and a |subst|
which works, we must figure out how to transport values between
provably but not judgmentally equal types.

The situation is particularly galling when you think how a type like
|P f| could possibly depend on a function |f|. If all |P| ever does with
|f| is to \emph{apply} it, then of course |P| respects extensional
equality. If types can only depend on values by observing them, then
there should be a systematic way to show that transportability between
types respects equality-up-to-observation.

But does the hypothesis of the previous sentence hold? Consider

%format Favourite = "\D{Favourite}"
%format favourite = "\C{favourite}"
\begin{code}
data Favourite : (Nat -> Nat) -> Set where
  favourite : Favourite (\ x -> zero +Nat x)
\end{code}

We may certainly prove that |\ x -> zero +Nat x| and |\ x -> x +Nat
zero| agree on all inputs. But is there a canonical inhabitant of
|Favourite (\ x -> x +Nat zero)|. If so, it can only be |favourite|,
for that is the only constructor, but |favourite| does not have that
type because the two functions are not judgmentally equal. The trouble
is that by using the power to `focus' a constructor's return type on
specific indices, |Favourite| is an \emph{intensional} predicate,
holding only for a specific implementation of a particular
function. We cannot expect a type theory with intensional predicates
to admit a sensible notion of extensional equality. Let us do away
with them! If, instead, we reformulate |Favourite| in the Henry Ford
tradition,
%format Favourite' = "\D{Favourite}"
%format favourite' = "\C{favourite}"
\begin{code}
data Favourite' (f : Nat -> Nat) : Set where
  favourite' : (\ x -> zero +Nat x) == f -> Favourite' f
\end{code}
then our definition of |Favourite'| becomes just as intensional as
our equality. If, somehow, |==| were to admit extensionality, we could
certainly show that |Favourite'| respects |==| just by transitivity.

