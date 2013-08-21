%if False
\begin{code}
module IR where

open import Vec public
open import Normal public
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
enough to be a |Set| itself!
