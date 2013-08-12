%if False

\begin{code}

module Vec where

open import Basics public

\end{code}

%endif

%format . = "."
%format Set = "\D{Set}"
%format Set1 = Set "_{\D{1}}"
%format List = "\D{List}"
%format <> = "\C{\langle\rangle}"
%format , = "\red{,}\,"
%format Nat = "\D{\mathbb{N}}"
%format zero = "\C{zero}"
%format suc = "\C{suc}"
%format id = "\F{id}"
%format o = "\F{\circ}"

It might be easy to mistake this chapter for a bland introduction to
dependently typed programming based on the yawning-already example of
lists indexed by their length, known to their friends as
\emph{vectors}, but in fact, vectors offer us a way to start analysing
data structures into `shape and contents'. Indeed, the typical
motivation for introducing vectors is exactly to allow types to
express shape invariants.


\section{Zipping Lists of Compatible Shape}

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


%format Sg = "\D{\Upsigma}"
%format fst = "\F{fst}"
%format snd = "\F{snd}"
%format * = "\F{\times}"
%format + = "\F{+}"
%format _+_ = "\_\!" + "\!\_"
%format vv = "\raisebox{0.02in}{\ensuremath{\F{\scriptstyle\mathrm{V}}}}"
%format One = "\D{One}"
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

Our |zip0| function imposes a `garbage in? garbage out!' deal, but
logically, we might want to ensure the obverse: if we supply
meaningful input, we want to be sure of meaningful output. But what is
meaningful input? Lists the same length!  Locally, we have a
\emph{relative} notion of meaningfulness. What is meaningful output?
We could say that if the inputs were the same length, we expect output
of that length. How shall we express this property? We could
externalise it in some suitable program logic, first explaining what
`length' is.

\nudge{The number of c's in |suc| is a long standing area of open
warfare.}
\nudge{Agda users tend to use lowercase-vs-uppercase to distinguish things in |Set|s from things which are or manipulate |Set|s.}
\nudge{The pragmas let you use Arabic numerals.}
\begin{code}
data Nat : Set where
  zero  :         Nat
  suc   : Nat ->  Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}
\end{code}

%format length = "\F{length}"
\begin{code}
length : {X : Set} -> List X -> Nat
length <>        = zero
length (x , xs)  = suc (length xs)
\end{code}

Informally,\footnote{by which I mean, not to a computer}
we might state and prove something like
\[
  \forall |ss|, |ts|.\;
  |length ss| = |length ts| \Rightarrow |length (zip0 ss ts) = length ss|
\]
by structural induction~\citep{burstall:induction} on |ss|, say.
Of course, we could just as well have concluded that
|length (zip0 ss ts) = length ts|, and if we carry on |zip0|ping, we
shall accumulate a multitude of expressions known to denote the same
number.

Matters get worse if we try to work with matrices as lists of lists (a
matrix is a column of rows, say).  How do we express rectangularity?
Can we define a function to compute the dimensions of a matrix? Do we
want to?  What happens in degenerate cases? Given \(m\), \(n\), we
might at least say that the outer list has length \(m\) and that all
the inner lists have length \(n\). Talking about matrices gets easier
if we imagine that the dimensions are \emph{prescribed}---to be checked,
not measured.


\section{Vectors}

Dependent types allow us to \emph{internalize} length invariants in
lists, yielding \emph{vectors}. The index describes the shape of the
list, thus offers no real choice of constructors.

%format Vec = "\D{Vec}"
\begin{code}
data Vec (X : Set) : Nat -> Set where
  <>   :                               Vec X zero
  _,_  : {n : Nat} -> X -> Vec X n ->  Vec X (suc n)
\end{code}

\paragraph{Parameters and indices.} In the above definition, the
element type is abstracted uniformly as |X| across the whole
thing. The definition could be instantiated to any particular set |X|
and still make sense, so we say that |X| is a \emph{parameter} of the
definition. Meanwhile, |Vec|'s second argument varies in each of the
three places it is instantiated, so that we are really making a
mutually inductive definition of the vectors at every possible length,
so we say that the length is an \emph{index}. In an Agda |data|
declaration head, arguments left of |:| (|X| here) scope over all
constructor declarations and must be used uniformly in constructor
return types, so it is sensible to put parameters left of
|:|. However, as we shall see, such arguments may be freely
instantiated in \emph{recursive} positions, so we should not presume
that they are necessarily parameters.

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
%format (HOLE (x) n) = { x } "\!_{" n "}"
%format GAP = "\;"
\begin{spec}
zip1 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip1 ss ts = (HOLE GAP 0)
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
%format Goal = "\mathkw{Goal}"
\begin{spec}
Goal  : Vec (Sg .S (\ _ → .T)) .n
-- \hspace*{-0.3in}------------------------------------------------------------------
ts    : Vec .T .n
ss    : Vec .S .n
.T    : Set
.S    : Set
.n    : Nat
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
zip1 ss ts = (HOLE (ss [C-c C-c]) 0)
\end{spec}

Agda responds by editing our source code, replacing the single line of
defintion by two more specific cases.

\begin{spec}
zip1 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip1 <> ts = (HOLE GAP 0)
zip1 (x , ss) ts = (HOLE GAP 1)
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
zip1 <> <> = (HOLE GAP 0)
zip1 (x , ss) ts = (HOLE GAP 1)
\end{spec}
and in the |suc| case,
\begin{spec}
zip1 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip1 <> <> = (HOLE GAP 0)
zip1 (x , ss) (x1 , ts) = (HOLE GAP 1)
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


%format iso = "\cong"

What just happened? We made |Vec|, a version of |List|, indexed by
|Nat|, and suddenly became able to work with `elements in
corresponding positions' with some degree of precision. That worked
because |Nat| describes the \emph{shape} of lists: indeed |Nat iso
List One|, instantiating the |List| element type to the type |One|
with the single element |<>|, so that the only information present is
the shape. Once we fix the shape, we acquire a fixed notion of
position.


%format vec = "\F{vec}"
%format vapp = "\F{vapp}"
\begin{exe}[|vec|]
Complete the implementation of
\begin{spec}
vec : forall {n X} -> X -> Vec X n
vec {n} x = ?
\end{spec}
using only control codes and arrow keys.
\nudge{Why is there no specification?}
%if False
\begin{code}
vec : forall {n X} -> X -> Vec X n
vec {zero} x = <>
vec {suc n} x = x , vec x
\end{code}
%endif
(Note the brace notation, making the implicit |n| explicit. It is not unusual
for arguments to be inferrable at usage sites from type information, but
none the less computationally relevant.)
\end{exe}

%format vapp = "\F{vapp}"
\begin{exe}[vector application]
Complete the implementation of
\begin{spec}
vapp :  forall {n S T} -> Vec (S -> T) n -> Vec S n -> Vec T n
vapp fs ss = ?
\end{spec}
using only control codes and arrow keys. The function should apply
the functions from its first input vector to the arguments in corresponding
positions from its second input vector, yielding values in corresponding positions
in the output.
%if False
\begin{code}
vapp :  forall {n S T} -> Vec (S -> T) n -> Vec S n -> Vec T n
vapp <> <> = <>
vapp (f , fs) (s , ss) = f s , vapp fs ss
\end{code}
%endif
\end{exe}

%format vmap = "\F{vmap}"
%format zip2 = zip0
\begin{exe}[|vmap|]
Using |vec| and |vapp|, define the functorial `map' operator for vectors,
applying the given function to each element.
\begin{spec}
vmap : forall {n S T} -> (S -> T) -> Vec S n -> Vec T n
vmap f ss = ?
\end{spec}
%if False
\begin{code}
vmap : forall {n S T} -> (S -> T) -> Vec S n -> Vec T n
vmap f ss = vapp (vec f) ss
\end{code}
%endif
Note that you can make Agsy notice a defined function by writing its name
as a hint in the relevant hole before you |[C-c C-a]|.
\end{exe}

\begin{exe}[|zip2|]
Using |vec| and |vapp|, give an alternative definition of |zip2|.
\begin{spec}
zip2 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip2 ss ts = ?
\end{spec}
%if False
\begin{code}
zip2 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip2 ss ts = vapp (vapp (vec _,_) ss) ts
\end{code}
%endif
\end{exe}

\begin{exe}[Finite sets and projection from vectors]
We may define a type of finite sets, suitable for indexing into vectors, as follows:
\begin{code}
data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc  : {n : Nat} -> Fin n -> Fin (suc n)
\end{code}

Implement projection:
%format proj = "\F{proj}"
\begin{spec}
proj : forall {n X} -> Vec X n -> Fin n -> X
proj xs i = ?
\end{spec}
%if False
\begin{code}
proj : forall {n X} -> Vec X n -> Fin n -> X
proj <> ()
proj (x , xs) zero = x
proj (x , xs) (suc i) = proj xs i
\end{code}
%endif

Implement, tabulation, the inverse of projection.
%format tabulate = "\F{tabulate}"
\begin{spec}
tabulate : forall {n X} -> (Fin n -> X) -> Vec X n
tabulate {n} f = ?
\end{spec}
Hint: think higher order.
%if False
\begin{code}
tabulate : forall {n X} -> (Fin n -> X) -> Vec X n
tabulate {zero} _ = <>
tabulate {suc n} f = f zero , tabulate (f o suc)
\end{code}
%endif
\end{exe}


\section{Applicative and Traversable Structure}

%format EndoFunctor = "\D{EndoFunctor}"
%format Applicative = "\D{Applicative}"
%format Monad = "\D{Monad}"
%format map = "\F{map}"
%format pure = "\F{pure}"
%format <*> = "\F{\circledast}"
%format _<*>_ = "\_\!" <*> "\!\_"
%format applicativeEndoFunctor = "\F{applicativeEndoFunctor}"
%format traversableEndoFunctor = "\F{traversableEndoFunctor}"
%format applicativeVec = "\F{applicativeVec}"
%format endoFunctorVec = "\F{endoFunctorVec}"
%format applicativeFun = "\F{applicativeFun}"
%format monadApplicative = "\F{monadApplicative}"
%format return = "\F{return}"
%format >>= = "\F{>\!\!>\!\!=}"
%format _>>=_ = "\_\!" >>= "\!\_"

The |vec| and |vapp| operations from the previous section equip
vectors with the structure of an \emph{applicative functor}.
\nudge{For now, I shall just work in |Set|, but we should remember
to break out and live, categorically, later.}
Before we get to |Applicative|, let us first say what is an |EndoFunctor|:
\nudge{Why |Set1|?}
\begin{code}
record EndoFunctor (F : Set -> Set) : Set1 where
  field
    map  : forall {S T} -> (S -> T) -> F S -> F T
open EndoFunctor {{...}} public
\end{code}
The above record declaration creates new types |EndoFunctor F| and a new
\emph{module}, |EndoFunctor|, containing a function, |EndoFunctor|.|map|,
which projects the |map|
field from a record. The |open| declaration brings |map| into top level scope,
and the |{{...}}| syntax indicates that |map|'s record argument is an
\emph{instance argument}. Instance arguments are found by searching the context
for something of the required type, succeeding if exactly one candidate is found.

Of course, we should ensure that such structures should obey the functor laws,
with |map| preserving identity and composition. Dependent types allow us to
state and prove these laws, as we shall see shortly.

First, however, let us refine |EndoFunctor| to |Applicative|.
\begin{code}
record Applicative (F : Set -> Set) : Set1 where
  infixl 2 _<*>_
  field
    pure    : forall {X} -> X -> F X
    _<*>_   : forall {S T} -> F (S -> T) -> F S -> F T
  applicativeEndoFunctor : EndoFunctor F
  applicativeEndoFunctor = record { map = _<*>_ o pure }
open Applicative {{...}} public
\end{code}
The |Applicative F| structure decomposes |F|'s |map| as the ability to make
`constant' |F|-structures and closure under application.

Given that instance arguments are collected from the context, let us seed
the context with suitable candidates for |Vec|:
\begin{code}
applicativeVec  : forall {n} -> Applicative \ X -> Vec X n
applicativeVec  = record { pure = vec; _<*>_ = vapp }
endoFunctorVec  : forall {n} -> EndoFunctor \ X -> Vec X n
endoFunctorVec  = applicativeEndoFunctor
\end{code}
Indeed, the definition of |endoFunctorVec| already makes use of way
|itsEndoFunctor| searches the context and finds |applicativeVec|.

There are lots of applicative functors about the place. Here's
\nudge{|proj| and |tabulate| turn the |vec| and |vapp| applicative into this one.}
another
famous one:
\begin{code}
applicativeFun : forall {S} -> Applicative \ X -> S -> X
applicativeFun = record
  {  pure    = \ x s -> x              -- also known as K (drop environment)
  ;  _<*>_   = \ f a s -> f s (a s)    -- also known as S (share environment)
  }
\end{code}

Monadic structure induces applicative structure:
\begin{code}
record Monad (F : Set -> Set) : Set1 where
  field
    return  : forall {X} -> X -> F X
    _>>=_   : forall {S T} -> F S -> (S -> F T) -> F T
  monadApplicative : Applicative F
  monadApplicative = record
    {  pure   = return
    ;  _<*>_  = \ ff fs -> ff >>= \ f -> fs >>= \ s -> return (f s) }
open Monad {{...}} public
\end{code}

%format monadVec =  "\F{monadVec}"
\begin{exe}[|Vec| monad]
Construct a |Monad| satisfying the |Monad| laws
\begin{spec}
monadVec : {n : Nat} -> Monad \ X -> Vec X n
monadVec = ?
\end{spec}
such that |monadApplicative| agrees extensionally with |applicativeVec|.
%if False
\begin{code}
monadVec : {n : Nat} -> Monad \ X -> Vec X n
monadVec = record
  {   return  = pure
  ;   _>>=_   = \ fs k -> diag (map k fs)
  }  where
     tail : forall {n X} -> Vec X (suc n) -> Vec X n
     tail (x , xs) = xs
     diag : forall {n X} -> Vec (Vec X n) n -> Vec X n
     diag <>                = <>
     diag ((x , xs) , xss)  = x , diag (map tail xss)
\end{code}
%endif
\end{exe}

\begin{exe}[|Applicative| identity and composition]
Show by construction that the identity endofunctor is |Applicative|, and that
the composition of |Applicative|s is |Applicative|.
%format applicativeId = "\F{applicativeId}"
%format applicativeComp = "\F{applicativeComp}"
\begin{spec}
applicativeId : Applicative id
applicativeId = ?

applicativeComp : forall {F G} -> Applicative F -> Applicative G -> Applicative (F o G)
applicativeComp aF aG = ?
\end{spec}
%if False
\begin{code}
applicativeId : Applicative id
applicativeId = record { pure = id; _<*>_ = id }

applicativeComp : forall {F G} -> Applicative F -> Applicative G -> Applicative (F o G)
applicativeComp aF aG = record
  {  pure   = \ x    -> pure {{aF}} (pure x)
  ;  _<*>_  = \ f s  -> pure {{aF}} _<*>_ <*> f <*> s
  }
\end{code}
%endif
\end{exe}

%format Monoid = "\D{Monoid}"
%format neut = "\F{\varepsilon}"
%format & = "\bullet"
%format _&_ = "\us{" & "}"
%format monoidApplicative = "\F{monoidApplicative}"
\begin{exe}[|Monoid| makes |Applicative|]
Let us give the signature for a monoid thus:
\begin{spec}
record Monoid (X : Set) : Set where
  infixr 4 _&_
  field
    neut  : X
    _&_   : X -> X -> X
  monoidApplicative : Applicative \ _ -> X
  monoidApplicative = ?
open Monoid {{...}} public -- it's not obvious that we'll avoid ambiguity
\end{spec}
Complete the |Applicative| so that it behaves like the |Monoid|.
%if False
\begin{code}
record Monoid (X : Set) : Set where
  infixr 4 _&_
  field
    neut  : X
    _&_   : X -> X -> X
  monoidApplicative : Applicative \ _ -> X
  monoidApplicative = record { pure = \ x -> neut; _<*>_ = _&_ }
open Monoid {{...}} public -- it's not obvious that we'll avoid ambiguity
\end{code}
%endif
\end{exe}

\begin{exe}[|Applicative| product]
Show by construction that the pointwise product of |Applicative|s is
|Applicative|.
\end{exe}

%format Traversable = "\D{Traversable}"
%format traverse = "\F{traverse}"
%format traversableVec = "\F{traversableVec}"
\begin{code}
record Traversable (F : Set -> Set) : Set1 where
  field
    traverse :  forall {G S T}{{AG : Applicative G}} ->
                (S -> G T) -> F S -> G (F T)
  traversableEndoFunctor : EndoFunctor F
  traversableEndoFunctor = record { map = traverse }
open Traversable {{...}} public
\end{code}

%format vtr = "\F{vtr}"
\nudge{The explicit |aG| became needed after I introduced the
|applicativeId| exercise, making resolution ambiguous.}
\begin{code}
traversableVec : {n : Nat} -> Traversable \ X -> Vec X n
traversableVec = record { traverse = vtr } where
  vtr :  forall {n G S T}{{_ : Applicative G}} ->
         (S -> G T) -> Vec S n -> G (Vec T n)
  vtr {{aG}} f <>        = pure {{aG}} <>
  vtr {{aG}} f (s , ss)  = pure {{aG}} _,_ <*> f s <*> vtr f ss
\end{code}

%format transpose = "\F{transpose}"
\begin{exe}[|transpose|]
Implement matrix transposition in one line.
\begin{spec}
transpose : forall {m n X} -> Vec (Vec X n) m -> Vec (Vec X m) n
transpose = ?
\end{spec}
%if False
\begin{code}
transpose : forall {m n X} -> Vec (Vec X n) m -> Vec (Vec X m) n
transpose = traverse id
\end{code}
%endif
\end{exe}

%format crush = "\F{crush}"
We may define the |crush| operation, accumulating values in a monoid stored in
a |Traversable| structure:
\nudge{I was going to set this as an exercise, but it's mostly instructive
in how to override implicit and instance arguments.}
\begin{code}
crush :  forall {F X Y}{{TF : Traversable F}}{{M : Monoid Y}} ->
         (X -> Y) -> F X -> Y
crush {{M = M}} =
  traverse {T = One}{{AG = monoidApplicative {{M}}}}  -- |T| arbitrary
\end{code}
Amusingly, we must tell Agda which |T| is intended when viewing |X -> Y| as
|X -> (\ _ -> Y) T|. In a Hindley-Milner
language, such uninferred things are unimportant because they are in any case
parametric. In the dependently typed setting, we cannot rely on quantification
being parametric (although in the absence of typecase, quantification over
types cannot help so being).

\begin{exe}[|Traversable| functors]
Show that |Traversable| is closed under identity and composition.
What other structure does it preserve?
\end{exe}


\section{|Sg|-types and Other Equipment}

Before we go any further, let us establish that the type |Sg (S : Set)
(T : S -> Set)| has elements |(s : S) , (t : T s)|, so that the type
of the second component depends on the value of the first. From |p :
Sg S T|, we may project |fst p : S| and |snd p : T (fst p)|, but I
also define |vv| to be a low precedence uncurrying operator, so that |vv \
s t -> ...| gives access to the components.

On the one hand, we may take |S * T = Sg S \ _ -> T|
and generalize the binary product to its dependent version. On the
other hand, we can see |Sg S T| as generalising the binary sum to an |S|-ary
sum, which is why the type is called |Sg| in the first place.

We can recover the binary sum (coproduct) by defining a two element type:
%format Two = "\D{Two}"
%format tt = "\C{t\!t}"
%format ff = "\C{f\!f}"
\begin{spec}
data Two : Set where tt ff : Two
\end{spec}

It is useful to define a conditional operator, indulging my penchant for giving
infix operators three arguments,
%format <?> = "\F{\left<?\right>}"
%format _<?>_ = "\_\!" <?> "\!\_"
\begin{spec}
_<?>_ : forall {l}{P : Two -> Set l} -> P tt -> P ff -> (b : Two) -> P b
(t <?> f) tt = t
(t <?> f) ff = f
\end{spec}
for we may then define:
\begin{spec}
_+_ : Set -> Set -> Set
S + T = Sg Two (S <?> T)
\end{spec}
Note that |<?>| has been defined to work at all levels of the predicative
hierarchy, so that we can use it to choose between |Set|s, as well as between
ordinary values. |Sg| thus models both choice and pairing in data structures.
That is, |Sg| generalizes binary product to the dependent case, and binary sum
to arbitrary arity. I advise calling a |Sg|-type neither a `dependent sum' nor
a `dependent product' (for a dependent function type is a something-adic product),
but rather a `dependent pair type'.


\section{Arithmetic}

I don't know about you, but I find I do a lot more arithmetic with
types than I do with numbers, which is why I have used |*| and |+| for
|Set|s. However, we shall soon need a little arithmetic for the sizes
of things.

%format +Nat = + "_{\!" Nat "}"
%format *Nat = * "_{\!" Nat "}"
%format _+Nat_ = "\us{" +Nat "}"
%format _*Nat_ = "\us{" *Nat "}"
\begin{exe}[unary arithmetic]
Implement addition and multiplication for numbers.
\begin{spec}
_+Nat_ : Nat -> Nat -> Nat
x +Nat y = ?

_*Nat_ : Nat -> Nat -> Nat
x *Nat y = ?
\end{spec}
%if False
\begin{code}
_+Nat_ : Nat -> Nat -> Nat
zero +Nat y = y
suc x +Nat y = suc (x +Nat y)

_*Nat_ : Nat -> Nat -> Nat
zero *Nat y = zero
suc x *Nat y = y +Nat (x *Nat y)
\end{code}
%endif
\end{exe}

%include Normal.lagda
%include Proving.lagda
%include NormT.lagda
%include NormF.lagda
