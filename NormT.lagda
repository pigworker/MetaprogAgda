%if False
\begin{code}

module NormT where

open import Proving public

\end{code}
%endif



\section{Laws for |Applicative| and |Traversable|}

Developing the laws for |Applicative| and |Traversable| requires more
substantial chains of equational reasoning. Here are some operators
which serve that purpose, inspired by work from Lennart Augustsson and
Shin-Cheng Mu.

%format =!! = "\F{=\!\!\![}"
%format >> = "\F{\rangle}"
%format _=!!_>>_ = "\_" =!! "\_" >> "\!\_"
%format !!= = "\F{]\!\!\!=}"
%format << = "\F{\langle}"
%format _<<_!!=_ = "\_\!" << "\_" !!= "\_"
%format <QED> = "\F{\square}"
%format _<QED> = "\_" <QED>
\begin{spec}
_=!!_>>_ : forall {l}{X : Set l}(x : X){y z} -> x == y -> y == z -> x == z
_ =!! refl >> q = q

_<<_!!=_ : forall {l}{X : Set l}(x : X){y z} -> y == x -> y == z -> x == z
_ << refl !!= q = q

_<QED> : forall {l}{X : Set l}(x : X) -> x == x
x <QED> = refl

infixr 1 _=!!_>>_ _<<_!!=_ _<QED>
\end{spec}

These three build right-nested chains of equations. Each requires an explicit
statement of where to start. The first two step along an equation used
left-to-right or right-to-left, respectively, then continue the chain. Then,
|x <QED>| marks the end of the chain.

Meanwhile, we may need to rewrite in a context whilst building these proofs.
In the expression syntax, we have nothing like |rewrite|.
%format cong = "\F{cong}"
\begin{spec}
cong : forall {k l}{X : Set k}{Y : Set l}(f : X -> Y){x y} -> x == y -> f x == f y
cong f refl = refl
\end{spec}

Thus armed, let us specify what makes an |Applicative| acceptable, then
show that such a thing is certainly a |Functor|.
\nudge{I had to $\eta$-expand |o| in lieu of subtyping.}
%format ApplicativeOKP = "\D{ApplicativeOKP}"
%format lawId = "\F{lawId}"
%format lawCo = "\F{lawCo}"
%format lawHom = "\F{lawHom}"
%format lawCom = "\F{lawCom}"
%format applicativeEndoFunctorOKP = "\F{applicativeEndoFunctorOKP}"
\begin{code}
record ApplicativeOKP F {{AF : Applicative F}} : Set1 where
  field
    lawId :   forall {X}(x : F X) ->
      pure {{AF}} id <*> x == x
    lawCo :   forall {R S T}(f : F (S -> T))(g : F (R -> S))(r : F R) ->
      pure {{AF}} (\ f g -> f o g) <*> f <*> g <*> r == f <*> (g <*> r)
    lawHom :  forall {S T}(f : S -> T)(s : S) ->
      pure {{AF}} f <*> pure s == pure (f s)
    lawCom :  forall {S T}(f : F (S -> T))(s : S) ->
      f <*> pure s == pure {{AF}} (\ f -> f s) <*> f
  applicativeEndoFunctorOKP : EndoFunctorOKP F {{applicativeEndoFunctor}}
  applicativeEndoFunctorOKP = record
    {  endoFunctorId = lawId
    ;  endoFunctorCo = \ f g r ->
         pure {{AF}} f <*> (pure {{AF}} g <*> r)
           << lawCo (pure f) (pure g) r !!=
         pure {{AF}} (\ f g -> f o g) <*> pure f <*> pure g <*> r
           =!! cong (\ x -> x <*> pure g <*> r) (lawHom (\ f g -> f o g) f) >>
         pure {{AF}} (_o_ f) <*> pure g <*> r 
           =!! cong (\ x -> x <*> r) (lawHom (_o_ f) g) >>
         pure {{AF}} (f o g) <*> r
           <QED>
    }
\end{code}

\begin{exe}[|ApplicativeOKP| for |Vec|]
%format vecApplicativeOKP = "\F{vecApplicativeOKP}"
Check that vectors are properly applicative. You can get away with
|rewrite| for these proofs, but you might like to try the new tools.
%format vecApplicativeOKP = "\F{vecApplicativeOKP}"
\begin{spec}
vecApplicativeOKP : {n : Nat} -> ApplicativeOKP \ X -> Vec X n
vecApplicativeOKP = ?
\end{spec}
%if False
\begin{code}
vecApplicativeOKP : {n : Nat} -> ApplicativeOKP \ X -> Vec X n
vecApplicativeOKP = record
  {  lawId   = appId
  ;  lawCo   = appCo
  ;  lawHom  = appHom
  ;  lawCom  = appCom
  }  where
  appId : forall {n X}(xs : Vec X n) -> vapp (vec id) xs == xs
  appId <>                          = refl
  appId (x , xs)  rewrite appId xs  = refl
  appCo :  forall {n R S T}
           (f : Vec (S -> T) n) (g : Vec (R -> S) n)(xs : Vec R n) ->
           vapp (vapp (vapp (vec (\ f g -> f o g)) f) g) xs == vapp f (vapp g xs)
  appCo <>        <>        <>                                = refl
  appCo (f , fs)  (g , gs)  (x , xs)  rewrite appCo fs gs xs  = refl
  appHom :  forall {n S T} (f : S -> T) (s : S) →
            vapp {n} (vec f) (vec s) == vec (f s)
  appHom {zero}   f s                         = refl
  appHom {suc n}  f s rewrite appHom {n} f s  = refl
  appCom :  forall {n S T} (f : Vec (S -> T) n) (s : S) ->
            vapp f (vec s) == vapp (vec (\ f → f s)) f
  appCom <> s = refl
  appCom (f , fs) s rewrite appCom fs s = refl
\end{code}
%endif
\end{exe}

Given that |traverse| is parametric in an |Applicative|, we should expect to
observe the corresponding naturality. We thus need a notion of
\emph{applicative homomorphism}, being a natural transformation which respects
|pure| and |<*>|. That is,
%format -:> = "\F{\dot{\to}}"
%format _-:>_ = "\us{" -:> "}"
%format AppHom = "\D{AppHom}"
%format respPure = "\F{resp}" pure
%format respApp = "\F{resp}" <*>
\begin{code}
_-:>_ : forall (F G : Set -> Set) -> Set1
F -:> G = forall {X} -> F X -> G X

record AppHom  {F}{{AF : Applicative F}}{G}{{AG : Applicative G}}
               (k : F -:> G) : Set1 where
  field
    respPure  : forall {X}(x : X) -> k (pure x) == pure x
    respApp   : forall {S T}(f : F (S -> T))(s : F S) -> k (f <*> s) == k f <*> k s
\end{code}

We may readily check that monoid homomorphisms lift to applicative homomorphisms.
%format monoidApplicativeHom = "\F{monoidApplicativeHom}"
%format MonoidHom.respNeut = MonoidHom . respNeut
%format MonoidHom.resp& = MonoidHom . resp&
\begin{code}
monoidApplicativeHom :
  forall {X}{{MX : Monoid X}}{Y}{{MY : Monoid Y}}
  (f : X -> Y){{hf : MonoidHom f}} ->
  AppHom {{monoidApplicative {{MX}}}} {{monoidApplicative {{MY}}}} f
monoidApplicativeHom f {{hf}} = record
  {  respPure  = \ x -> MonoidHom.respNeut hf
  ;  respApp   = MonoidHom.resp& hf
  }
\end{code}

\begin{exe}[homomorphism begets applicative]
Show that a homomorphism from |F| to |G| induces applicative structure
on their pointwise sum.
%format homSum = "\F{homSum}"
\begin{spec}
homSum :  forall {F G}{{AF : Applicative F}}{{AG : Applicative G}} ->
          (f : F -:> G) -> 
          Applicative \ X -> F X + G X
homSum {{AF}}{{AG}} f = ?
\end{spec}
%if False
\begin{code}
homSum :  forall {F G}{{AF : Applicative F}}{{AG : Applicative G}} ->
            (f : F -:> G) ->
            Applicative \ X -> F X + G X
homSum {{AF}}{{AG}} f = record {
   pure = _,_ tt o pure{{AF}}
  ; _<*>_ = vv (\ fk -> vv (\ fs -> tt , (fk <*> fs))
                        <?> (\ gs -> ff , (f fk <*> gs)))
            <?> (\ gk -> vv (\ fs -> ff , (gk <*> f fs))
                         <?> (\ gs -> ff , (gk <*> gs))) }
\end{code}
%endif
Check that your solution obeys the laws.
%format homSumOKP = "\F{homSumOKP}"
\begin{spec}
homSumOKP :  forall {F G}{{AF : Applicative F}}{{AG : Applicative G}} ->
             ApplicativeOKP F -> ApplicativeOKP G ->
             (f : F -:> G) -> AppHom f ->
             ApplicativeOKP _ {{homSum f}}
homSumOKP {{AF}}{{AG}} FOK GOK f homf = ?
\end{spec}
\end{exe}

Laws for |Traversable| functors are given thus:
%format TraversableOKP = "\D{TraversableOKP}"
\begin{code}
record TraversableOKP F {{TF : Traversable F}} : Set1 where
  field
    lawId   :  forall  {X}(xs : F X) -> traverse id xs == xs
    lawCo   :  forall  {G}{{AG : Applicative G}}{H}{{AH : Applicative H}}
                       {R S T}(g : S -> G T)(h : R -> H S)(rs : F R) ->
               let  EH : EndoFunctor H ; EH = applicativeEndoFunctor
               in   map{H} (traverse g) (traverse h rs)
                      ==
                    traverse{{TF}}{{applicativeComp AH AG}} (map{H} g o h) rs
    lawHom  :  forall {G}{{AG : Applicative G}}{H}{{AH : Applicative H}}
                      (h : G -:> H){S T}(g : S -> G T) -> AppHom h ->
                      (ss : F S) ->
                      traverse (h o g) ss == h (traverse g ss)
\end{code}

Let us now check the coherence property we needed earlier.
%format lengthContentsSizeShape = "\F{lengthContentsSizeShape}"
%format TraversableOKP.lawHom = TraversableOKP . lawHom
%format TraversableOKP.lawCo = TraversableOKP . lawCo
\begin{code}
lengthContentsSizeShape :
  forall  {F}{{TF : Traversable F}} -> TraversableOKP F ->
  forall  {X} (fx : F X) ->
  fst (contentsT fx) == sizeT (shapeT fx)
lengthContentsSizeShape tokF fx =
  fst (contentsT fx)
    <<  TraversableOKP.lawHom tokF {{monoidApplicative}} {{monoidApplicative}}
          fst one (monoidApplicativeHom fst) fx !!=
  sizeT fx
    <<  TraversableOKP.lawCo tokF {{monoidApplicative}}{{applicativeId}}
          (\ _ -> 1) (\ _ -> <>) fx !!=
  sizeT (shapeT fx) <QED>
\end{code}

We may now construct
\begin{code}
toNormal :  forall {F}{{TF : Traversable F}} -> TraversableOKP F ->
            forall {X} -> F X -> <! normalT F !>N X
toNormal tokf fx
  =  shapeT fx
  ,  subst (lengthContentsSizeShape tokf fx) (Vec _) (snd (contentsT fx))
\end{code}


%format fromNormal = "\F{fromNormal}"
%format Batch = "\F{Batch}"
\begin{exe}
Define |fromNormal|, reversing the direction of |toNormal|. One way to
do it is to define what it means to be able to build something from a
batch of contents.
\begin{code}
Batch : Set -> Set -> Set
Batch X Y = Sg Nat \ n -> Vec X n -> Y
\end{code}
Show |Batch X| is applicative. You can then use |traverse| on a shape
to build a |Batch| job which reinserts the contents. As above, you will
need to prove a coherence property to show that the contents vector in
your hand has the required length. Warning: you may encounter a consequence
of defining |sizeT| via |crush| with ignored target type |One|, and
need to prove that you get the same answer if you ignore something else.
Agda's `Toggle display of hidden arguments' menu option may help you detect
that scenario.
%if False
\begin{code}
chop : forall {X} m {n} -> Vec X (m +Nat n) -> Vec X m * Vec X n
chop zero xs = <> , xs
chop (suc m) (x , xs) with chop m xs
... | ys , zs = (x , ys) , zs

batchApplicative : {X : Set} -> Applicative (Batch X)
batchApplicative {X} = record
  {  pure   =  \ y -> zero , \ _ -> y
  ;  _<*>_  =  vv \ m f -> vv \ n g ->
       m +Nat n , \ xs -> let yszs = chop m xs in f (fst yszs) (g (snd yszs))
  }

fstHom' : forall {X} -> AppHom {{batchApplicative{X}}}{{monoidApplicative}} fst
fstHom' = record
  {  respPure  = \ _ -> refl
  ;  respApp   = \ _ _ -> refl
  }

eno : forall {X} -> Vec X 1 -> X
eno (x , <>) = x

stnetnocT :  forall {X F}{{TF : Traversable F}} -> F One -> Batch X (F X)
stnetnocT {X}{{TF}} s = traverse {{TF}}{{batchApplicative{X}}} (\ _ -> 1 , eno) s

lengthStnetnocSizeShape :
  forall  {F}{{TF : Traversable F}} -> TraversableOKP F ->
  forall  (s : F One){X} ->
  fst (stnetnocT{X} s) == sizeT s
lengthStnetnocSizeShape tokF s {X} =
  fst (stnetnocT{X} s)
    <<  TraversableOKP.lawHom tokF {{batchApplicative}}{{monoidApplicative}}
          fst (\ _ -> 1 , eno) fstHom' s !!=
  traverse {T = X} {{monoidApplicative}} (\ _ -> 1) s
    =!! TraversableOKP.lawCo tokF {{applicativeId}}{{monoidApplicative}}{S = X}
         (\ _ -> <>) (\ _ -> 1) s >>
  sizeT s <QED>

fromNormal :  forall {F}{{TF : Traversable F}} -> TraversableOKP F ->
              forall {X} -> <! normalT F !>N X -> F X
fromNormal tokf {X}(s , xs) with stnetnocT {X} s | lengthStnetnocSizeShape tokf s {X}
fromNormal {{TF}} tokf (s , xs) | ._ , c | refl = c xs
\end{code}
%endif
\end{exe}

Showing that |toNormal| and |fromNormal| are mutually inverse looks
like a tall order, given that the programs have been glued together
with coherence conditions. At time of writing, it remains undone.
When I see a mess like that, I wonder whether replacing indexing by
the measure of size might help.
