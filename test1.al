import "test1.al";
import "test2.al";
-- import "../test2.al";

data F; data T;

-- data x y z;

-- a Z + a Z;
-- a (S b) + a (S c):
--    a b + a c.

data #+ n;
a `+ Z` a;
a `+ (S b)` (S c):
    a `+ b` c.

a b + a c:
    b `+ a` c.


data #* a;
Z `* (S a)` Z;
(S b) `* (S a)` (S d):
    b `* (S a)` c.
    c `+ a` d.

[] `Map f` [];
[x . xs] `Map f` [y . ys]:
   -- `Dup f` f'.
   x `f` y.
   xs `Map f` ys....


{ |A; |B } = |C;
|X = |Y;

a b `@` c d:
    a ~ c.
    b ~ d.

-- can create anonymous scopes like so:
`@`:
    `~init`;
    `~loop`;
    `~term`;
    `Rev`: `~init`.

x `Qux` y:
    ~ x.
    ~ y.

x `Consume3`:
    `Dup 3` x.

-- Z Z +;