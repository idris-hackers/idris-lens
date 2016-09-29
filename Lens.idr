module Lens

import Control.Category

%access public export

-- Store comonad

data Store s a = MkStore (s -> a) s

interface Functor w => Comonad (w : Type -> Type) where
  extract : w a -> a
  extend : (w a -> b) -> w a -> w b

interface Comonad w => VerifiedComonad (w : Type -> Type) where
  comonadLaw1 : (wa : w a) ->
                extend extract wa = wa
  comonadLaw2 : (f : w a -> b) ->
                (wa : w a) ->
                extract (extend f wa) = f wa
  comonadLaw3 : (f : w b -> c) ->
                (g : w a -> b) ->
                (wa : w a) ->
                extend f (extend g wa) = extend (\d => f (extend g d)) wa

Functor (Store s) where
  map f (MkStore g a) = MkStore (f . g) a

Comonad (Store s) where
  extract (MkStore f a) = f a
  extend f (MkStore g a) = MkStore (\b => f (MkStore g b)) a

-- VerifiedComonad (Store s) where
--   comonadLaw1 (MkStore f a) = ?storeIdentityProof
--   comonadLaw2 f (MkStore g a) = Refl
--   comonadLaw3 f g (MkStore h a) = Refl

-- -- TODO: This is evil.
-- -- Supposedly (jonsterling) this definition used to work without the believe_me.
-- private
-- eta : (f : a -> b) -> f = (\c => f c)
-- eta g = believe_me Refl {g}

-- storeIdentityProof = proof
--   intros
--   rewrite eta f
--   trivial

pos : Store s a -> s
pos (MkStore _ s) = s

peek : s -> Store s a -> a
peek s (MkStore f _) = f s

peeks : (s -> s) -> Store s a -> a
peeks f (MkStore g s) = g (f s)

-- Lenses

data Lens a b = MkLens (a -> Store b a)

Category Lens where
  id = MkLens (MkStore id)
  (.) (MkLens f) (MkLens g) = MkLens (\a => case g a of
    MkStore ba b => case f b of
      MkStore cb c => MkStore (Prelude.Basics.(.) ba cb) c)

lens : (a -> b) -> (b -> a -> a) -> Lens a b
lens f g = MkLens (\a => MkStore (\b => g b a) (f a))

iso : (a -> b) -> (b -> a) -> Lens a b
iso f g = MkLens (\a => MkStore g (f a))

getL : Lens a b -> a -> b
getL (MkLens f) a = pos (f a)

setL : Lens a b -> b -> a -> a
setL (MkLens f) b = peek b . f

modL : Lens a b -> (b -> b) -> a -> a
modL (MkLens f) g = peeks g . f

mergeL : Lens a c -> Lens b c -> Lens (Either a b) c
mergeL (MkLens f) (MkLens g) = MkLens $ either (\a => map Left $ f a)
                                               (\b => map Right $ g b)

infixr 0 ^$
(^$) : Lens a b -> a -> b
(^$) = getL

infixr 4 ^=
(^=) : Lens a b -> b -> a -> a
(^=) = setL

infixr 4 ^%=
(^%=) : Lens a b -> (b -> b) -> a -> a
(^%=) = modL

fstLens : Lens (a,b) a
fstLens = MkLens $ \(a,b) => MkStore (\ a' => (a', b)) a

sndLens : Lens (a,b) b
sndLens = MkLens $ \(a,b) => MkStore (\ b' => (a, b')) b

-- Partial lenses

data PLens a b = MkPLens (a -> Maybe (Store b a))

Category PLens where
  id = MkPLens (Just . MkStore id)
  (.) (MkPLens f) (MkPLens g) = MkPLens (\a => do
    MkStore wba b <- g a
    MkStore wcb c <- f b
    pure (MkStore (wba . wcb) c))

plens : (a -> Either a (Store b a)) -> PLens a b
plens f = MkPLens $ either (const Nothing) Just . f

getPL : PLens a b -> a -> Maybe b
getPL (MkPLens f) a = map pos (f a)

justPL : PLens (Maybe a) a
justPL = MkPLens (\ma => do
  a <- ma
  pure (MkStore Just a))
