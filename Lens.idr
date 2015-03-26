module Lens

import Effect.State
import Effects

%access public

Lens : (s : Type) ->
       (t : Type) ->
       (a : Type) ->
       (b : Type) ->
       {default id f : Type -> Type} ->
       Type
Lens s t a b {f} = (a -> f b) -> s -> f t

Lens' : (s : Type) ->
        (a : Type) ->
        {default id f : Type -> Type} ->
        Type
Lens' s a {f} = Lens s s a a {f}

lens : Functor f => (s -> a) -> (s -> b -> t) -> Lens s t a b {f}
lens sa sbt afb s = sbt s <$> afb (sa s)

iso : Functor f => (s -> a) -> (b -> t) -> Lens s t a b {f}
iso f g afb s = g <$> afb (f s)

infixl 8 ^.

(^.) : s -> Lens' s a {f = const a} -> a
s ^. l = l id s

use : Lens' s a {f = const a} -> { [STATE s] } Eff a
use l = [| (^. l) get |]

_1 : Functor f => Lens (a, c) (b, c) a b {f}
_1 = lens fst (\(_, y) => \x => (x, y))

_2 : Functor f => Lens (a, b) (a, c) b c {f}
_2 = lens snd (\(x, _) => \y => (x, y))

infixr 4 $~

($~) : Lens s t a b -> (a -> b) -> s -> t
($~) = id

infixr 4 .~

(.~) : Lens s t a b -> b -> s -> t
(.~) = (. const)

infixr 4 <$~

(<$~) : Lens s t a b {f = Pair b} -> (a -> b) -> s -> (b, t)
(<$~) l f = l (\x => (f x, f x))

infixr 4 <.~

(<.~) : Lens s t a b {f = Pair b} -> b -> s -> (b, t)
(<.~) l x = l <$~ const x

infix 4 $=

($=) : Lens s t a b -> (a -> b) -> { [STATE s] ==> [STATE t] } Eff ()
l $= f = updateM (l $~ f)

infix 4 .=
(.=) : Lens s t a b -> b -> { [STATE s] ==> [STATE t] } Eff ()
l .= x = updateM (l .~ x)

infix 4 <$=
(<$=) : Lens s t a b {f = Pair b} ->
        (a -> b) ->
        { [STATE s] ==> [STATE t] } Eff b
l <$= f = case (l <$~ f) !get of
    (r, s) => do putM s
                 return r

infix 4 <.=
(<.=) : Lens s t a b {f = Pair b} -> b -> { [STATE s] ==> [STATE t] } Eff b
l <.= x = l <$= const x

private
example : runPure (id <$= (+ 10)) = 10
example = Refl
