%if False

\begin{code}

module Vec where

postulate
      Level : Set
      lzero  : Level
      lsuc   : Level -> Level
      lmax   : Level -> Level -> Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero  #-}
{-# BUILTIN LEVELSUC  lsuc   #-}
{-# BUILTIN LEVELMAX  lmax   #-}

\end{code}

%endif

%format Set = "\D{Set}"
%format List = "\D{List}"
%format <> = "\C{\langle\rangle}"
%format , = "\red{,}\,"
%format Nat = "\D{Nat}"
%format zero = "\C{zero}"
%format suc = "\C{suc}"

It might be easy to mistake this chapter for a bland introduction to
dependently typed programming based on the yawning-already example of
lists indexed by their length, known to their friends as
\emph{vectors}, but in fact, vectors offer us a way to start analysing
data structures into `shape and contents'. Indeed, the typical
motivation for introducing vectors is exactly to allow types to
express shape invariants.

Let us remind ourselves of the situation with ordinary \emph{lists},
which we may define in Agda as follows:
\nudge{Agda has a very simple lexer and very few special characters.
To a first approximation, ()\{\}; stand alone and everything else must be delimited with whitespace. }
\begin{code}
data List (X : Set) : Set where
  <>    :                 List X
  _,_   : X -> List X ->  List X

infixr 4 _,_
\end{code}

%if False
\begin{code}
record Sg {l : Level}(S : Set l)(T : S -> Set l) : Set l where
  constructor _,_
  field
    fst : S
    snd : T fst
open Sg
_*_ : {l : Level} -> Set l -> Set l -> Set l
S * T = Sg S \ _ -> T

record One {l : Level} : Set l where
  constructor _<>_
\end{code}
%endif

%format Sg = "\D{\Upsigma}"
%format fst = "\F{fst}"
%format snd = "\F{snd}"
%format * = "\F{\times}"
%format zip0 = "\F{zip}"

The classic operation which morally involves a shape invariant is |zip0|, taking
two lists, one of |S|s, the other of |T|s, and yielding a list of pairs in the product
|S * T| formed from elements \emph{in corresponding positions}. The trouble, of course,
is ensuring that positions correspond.
\nudge{The braces indicate that |S| and |T| are \emph{implicit arguments}. Agda will try
to infer them unless we override manually.}
\begin{code}
zip0 : {S T : Set} -> List S -> List T -> List (S * T)
zip0 <>        <>        = <>
zip0 (s , ss)  (t , ts)  = (s , t) , zip0 ss ts
zip0 _         _         = <>  -- a dummy value, for cases we should not reach
\end{code}

\paragraph{Overloading Constructors} Note that I have used `|,|' both
for tuple pairing and as list `cons'. Agda permits the overloading of
constructors, using type information to disambiguate them. Of course,
just because overloading is permitted, that does not make it
compulsory, so you may deduce that I have overloaded deliberately. As
data structures in the memory of a computer, I think of pairing and
consing as the same, and I do not expect data to tell me what they
mean. I see types as an external rationalisation imposed upon the raw
stuff of computation, to help us check that it makes sense (for
multiple possible notions of sense) and indeed to infer details (in
accordance with notions of sense). Those of you who have grown used to
thinking of type annotations as glorified comments will need to
retrain your minds to pay attention to them.

In order to talk about length, we shall need numbers. Agda does not treat
numbers primitively, so we must define them inductively.
\nudge{Wars have been fought over the number of |c|s in |suc|.}
Agda does at least provide pragmas which enable Arabic notation for unary
numbers.
\begin{code}
data Nat : Set where
  zero  : Nat
  suc   : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}
\end{code}

Note that |Nat| is isomorphic to |List One|, where |One| is a type
with one dull element. If you make the elements of a list carry no
information, then all you have left is the \emph{shape} of the list,
i.e., its length.

Now, that we have numbers, we may define lists indexed by length, often known as \emph{vectors}. The index describes the shape of the list, thus offers no real
choice of constructors.
%format Vec = "\D{Vec}"
\begin{code}
data Vec (X : Set) : Nat -> Set where
  <>   : Vec X zero
  _,_  : {n : Nat} -> X -> Vec X n -> Vec X (suc n)
\end{code}

%format zip1 = zip0
Let us now develop |zip1| for vectors, stating the length invariant
in the type.

\begin{spec}
zip1 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip1 ss ts = ?
\end{spec}

The length argument and the two element types are marked implicit by
default, as indicated by the |{..}| after the |forall|.  We write a
left-hand-side naming the explicit inputs, which we declare equal to
an unknown |?|. Loading the file with |[C-c C-l]|, we find that Agda
checks the unfinished program, turning the |?| into labelled braces,
\begin{spec}
zip1 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip1 ss ts = {!!}0
\end{spec}
and tells us, in the information window,
\begin{spec}
?0 : Vec (.S * .T) .n
\end{spec}
that the type of the `hole' corresponds to the return type we wrote.
The dots before |S|, |T|, and |n| indicate that these variables exist behind the
scenes, but have not been brought into scope by anything in the program text:
Agda can refer to them, but we cannot.

If we click between the braces to select that hole, and issue keystroke
|[C-c C-,]|, we will gain more information about the goal:
\begin{spec}
Goal: Vec (Sg .S (\ _ → .T)) .n
———————————————————————————————————————————————
ts  : Vec .T .n
ss  : Vec .S .n
.T  : Set
.S  : Set
.n  : Nat
\end{spec}
revealing the definition of |*| used in the goal, about which more shortly,
but also telling us about the types and visibility of variables in the
\emph{context}.

Our next move is to \emph{split} one of the inputs into cases. We can see from the
type information |ss  : Vec .S .n| that we do not know the length of |ss|, so it
might be given by either constructor. To see if Agda agrees, we type |ss| in the
hole and issue the `case-split' command |[C-c C-c]|.

\begin{spec}
zip1 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip1 ss ts = {ss [C-c C-c]}0
\end{spec}

Agda responds by editing our source code, replacing the single line of
defintion by two more specific cases.

\begin{spec}
zip1 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip1 <> ts = { }0
zip1 (x , ss) ts = { }1
\end{spec}

Moreover, we gain the refined type information
\begin{spec}
?0  : Vec (.S * .T) 0
?1  : Vec (.S * .T) (suc .n)
\end{spec}
which goes to show that the type system is now tracking what information
is learned about the problem by inspecting |ss|. This capacity for
\emph{learning by testing} is the paradigmatic characteristic of dependently
typed programming.

Now, when we split |ts| in the |0| case, we get
\begin{spec}
zip1 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip1 <> <> = { }0
zip1 (x , ss) ts = { }1
\end{spec}
and in the |suc| case,
\begin{spec}
zip1 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip1 <> <> = { }0
zip1 (x , ss) (x1 , ts) = { }1
\end{spec}
as the more specific type now determines the shape. Sadly, Agda is not
very clever\nudge{It's not even as clever as Epigram.} about choosing names,
but let us persevere. We have now made sufficient analysis of the input to
determine the output, and shape-indexing has helpfully ruled out shape mismatch.
It is now so obvious what must be output that Agda can figure it out for itself.
If we issue the keystroke |[C-c C-a]| in each hole, a type-directed program
search robot called `Agsy' tries to find an expression which will fit in the hole,
asssembling it from the available information without further case analysis.
We obtain a complete program.

\begin{spec}
zip1 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip1 <> <> = <>
zip1 (x , ss) (x1 , ts) = (x , x1) , zip1 ss ts
\end{spec}

I tend to $\alpha$-convert and realign such programs manually, yielding
\begin{code}
zip1 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip1 <>         <>        = <>
zip1 (s , ss)   (t , ts)  = (s , t) , zip1 ss ts
\end{code}
