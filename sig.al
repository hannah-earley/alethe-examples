

-- these would be appropriate for sigma, but do not work here because
-- of their ambiguity; as such, each sigma expression should have its
-- termini explicitly marked as halting
-- ! _;
-- ! _ a;
-- ! _ a b;
-- ! _ a b c;
-- ! _ a b c d;
-- ! _ a b c d e;
-- ! _ a b c d e f;
-- ! _ a b c d e f g;
-- ! _ a b c d e f g h;
-- ! _ a b c d e f g h i;
-- ! a b c d e f g h i _;
-- ! a b c d e f g h _;
-- ! a b c d e f g _;
-- ! a b c d e f _;
-- ! a b c d e _;
-- ! a b c d _;
-- ! a b c _;
-- ! a b _;
-- ! a _;
-- ! _;


data ,;
data , a;
data , a b;
data , a b c;
data , a b c d;

! Nil _ _;
Nil  [f g] x h = f [h g] x Nil;
Cons [f g] x h = g [f h] x Cons;

! Z _;
Z [f g] x h = f [h g] x Z;
S [f g] x h = g [f h] x S;



`@reverse`:
  ! Reverse l _; ! _ r' Reverse;
    Reverse l _
      = Nil [~Loop ~Next] (, (, _ _) l) Reverse;
    ~Loop [Reverse ~Next] (, (, r' r'') (l l' l'')) r
      = l [Reverse' ~Next] (, (r r' r'') (, l' l'')) ~Loop;
    ~Next [Reverse' ~Loop] (, r (, x xs)) Cons
      = Cons [Reverse ~Loop] (, (, x r) xs) ~Next;
    Reverse' [~Loop ~Next] (, r' (, _ _)) Nil
      = _ r' Reverse';


`@+`:
  ! #+ a b _; ! _ a c #+';
    #+ a b _                              = Z [~Loop ~Next] (, a     b _)       #+;
    ~Loop [+     ~Next] (, a (b b') c') c = b [+'    ~Next] (, a     b' (c c')) ~Loop;
    ~Next [+'    ~Loop] (, a b      c)  S = S [+     ~Loop] (, (S a) b c)       ~Next;
    #+'   [~Loop ~Next] (, a _      c)  Z = _ a c #+';
