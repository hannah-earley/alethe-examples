x `Id` x;
x `Seq y` x;

! Dup x;
`Dup x y` x' y':
    `Dup x` x'.
    `Dup y` y'.
`Dup x y z` x' y' z':
    `Dup x` x'.
    `Dup y` y'.
    `Dup z` z'.

! Discard x _; ! _ Discard;
c| Discard x _ = { c| _ Discard; Junk| x };

--# tuples

-- the following definitions demonstrate the exponential complexity
-- of the strategy algorithm...

data ,;
data , a;
data , a b;
data , a b c;
data , a b c d;
-- data , a b c d e;
-- data , a b c d e f;
-- data , a b c d e f g;
-- data , a b c d e f g h;

-- better to divide and conquer...
! #, a b c d e;
`Dup (, a b c d e)` (, a' b' c' d' e'):
    `Dup (, a b c)` (, a' b' c').
    `Dup (, d e)`   (, d' e').
! #, a b c d e f;
`Dup (, a b c d e f)` (, a' b' c' d' e' f'):
    `Dup (, a b c)` (, a' b' c').
    `Dup (, d e f)` (, d' e' f').
! #, a b c d e f g;
`Dup (, a b c d e f g)` (, a' b' c' d' e' f' g'):
    `Dup (, a b c d)` (, a' b' c' d').
    `Dup (, e f g)` (, e' f' g').
! #, a b c d e f g h;
`Dup (, a b c d e f g h)` (, a' b' c' d' e' f' g' h'):
    `Dup (, a b c d)` (, a' b' c' d').
    `Dup (, e f g h)` (, e' f' g' h').


data Garbage;
data Garbage a;
data Garbage a b;
data Garbage a b c;
data Garbage a b c d;

--# bools

data False;
data True;

False `Not` True;
True `Not` False;

`== False False` True;
`== False True`  False;
`== True  False` False;
`== True  True`  True;

a `CNot False` a;
a `CNot True`  a':
    a `Not` a'.

-- Toffoli
c `CCNot False b`     c;
c `CCNot True  False` c;
c `CCNot True  True`  c':
    c `Not` c'.

-- Fredkin
a b `CSwap False` a b;
a b `CSwap True`  b a;


--# nats

-- prelude:
--     Data Z;
--     Data S n;

-- iterative duplication
`DupIt a` b:
    ! ~L a     Z Z = ~L Z a     b.
      ~L (S a) b c = ~L a (S b) (S c);

n `Succ` (S n);

data EQ;
data GT;
data LT;

a b `Diff` ord delta min:
    ! ~Go a     b     Z   = ~Go ord delta min _.
      ~Go (S a) (S b) c   = ~Go a   b     (S c);
      ~Go Z     Z     min = ~Go EQ  Z     min _;
      ~Go (S a) Z     min = ~Go GT  (S a) min _;
      ~Go Z     (S b) min = ~Go LT  (S b) min _;

`Cmp a b` ord':
    a b `Diff` ord d m.
    `Dup ord` ord'.

a b <? p d m:
    a b `Diff` o d m.
    o  `~ d`     p.
    LT `~ (S a)` True;
    EQ `~ Z`     False;
    GT `~ (S a)` False;
a b >?  p d m:
    b a <? p d m.
a b <=? p d m: 
    b a <? p' d m.
    p `Not` p'.
a b >=? p d m: 
    a b <? p' d m.
    p `Not` p'.

`< a b` p':
    a b <? p d m.
    `Dup p` p'.
`> a b` p':
    b a <? p d m.
    `Dup p` p'.
`<= a b` p'':
    b a <? p d m.
    `Dup p` p'.
    p' `Not` p''.
`>= a b` p'':
    a b <? p d m.
    `Dup p` p'.
    p' `Not` p''.

`(< a) b` p: `< a b` p.
`(> a) b` p: `> a b` p.
`(<= a) b` p: `<= a b` p.
`(>= a) b` p: `>= a b` p.


a `+ b` c:
    ! ~Go a Z b      = ~Go c     b     Z.
      ~Go a b (S b') = ~Go (S a) (S b) b';

a `+Rec Z` a;
a `+Rec (S b)` (S c):
    a `+Rec b` c.

a `* (S b)` c:
    ! ~Go b Z a     = ~Go b c      Z.
      ~Go b c (S a) = ~Go b (S c') a:
          c `+ b` c'.

b `/ bc` c:
    c `* b` bc.
    b `* c` bc.

n `QuoRem d` q r:
    d-r `+ r` d.
    ! ~Go True Z n d = ~Go False (S q) d-r r.
      ~Go True q r d = ~Go p     (S q) r'  d':
          r d >=? p r' d'.

0  `Dig=Char` '0; 1  `Dig=Char` '1; 2  `Dig=Char` '2; 3  `Dig=Char` '3;
4  `Dig=Char` '4; 5  `Dig=Char` '5; 6  `Dig=Char` '6; 7  `Dig=Char` '7;
8  `Dig=Char` '8; 9  `Dig=Char` '9; 10 `Dig=Char` 'a; 11 `Dig=Char` 'b;
12 `Dig=Char` 'c; 13 `Dig=Char` 'd; 14 `Dig=Char` 'e; 15 `Dig=Char` 'f;

Z     `Digits b` [0];
(S n) `Digits b` [(S d) . ds]:
    ! ~Go b (S n) [] = ~Go b Z [(S d) . ds].
      ~Go b (S n) ds = ~Go b q [r     . ds]:
          (S n) `QuoRem b` q r.

n `Positional b` str:
    n `Digits b` ds.
    ds `Map Dig=Char` str.
n `Base10` str: n `Positional 10` str.
n `Binary` str: n `Positional 2`  str.
n `Hex`    str: n `Positional 16` str.


`@parity`:
    ! ~Go n b Z; ! ~Go Z b n;
     ~Go (S n) b n' = ~Go n b' (S n'):
        b `Not` b'.

    `Even n` p: ~~Go n True  Z = ~~Go Z p n.
    `Odd n`  p: ~~Go n False Z = ~~Go Z p n.

n >> b n/2:
    ! ~Go n         Z  = ~Go b     n/2 _.
      ~Go (S (S n)) n' = ~Go n     (S n');
      ~Go 1         n' = ~Go False n' _;
      ~Go 0         n' = ~Go True  n' _;
    

n ^2 n2:
    ! ~Go n     Z = ~Go Z n2.
      ~Go (S n) m = ~Go n (S k):
          m `+ n` l.
          l `+ n` k.
n ^2' n n2:
    ! ~Go n     Z  Z = ~Go Z n      n2.
      ~Go (S n) n' m = ~Go n (S n') (S k):
          m `+ n` l.
          l `+ n` k.
a b ^2+ n:
    ! ~Go n Z True = ~Go b aa False.
    ~Go (S b) a True = ~Go b' (S (S a)) p:
        b' `+ a` b.
        `> b' (S (S a))` p.
    aa >> True a.

n `Triangle` m:
    ! ~Go n     Z = ~Go Z m.
      ~Go (S n) m = ~Go n (S l):
          m `+ n` l.

-- Cantor pairing function
a b `Pair` n:
    ! ~Go n Z True = ~Go b (S a+b) False.
    ~Go n a+b True = ~Go n' (S a+b) p:
        n' `+ a+b` n.
        `> n' a+b` p.
    a `+ b` a+b.

(S n) `Fac` m:
    ! ~Go (S n)     1 = ~Go 1     m.
      ~Go (S (S n)) a = ~Go (S n) (S (S a')):
          a `* (S (S n))` (S (S a')).

a b `LucasSucc` b a+b:
    a `+ b` a+b.

n `Fib` a b:
    ! ~Go 0 1     n     = ~Go a     b Z.
      ~Go a (S b) (S n) = ~Go (S b) c n:
          a `+ (S b)` c.

0     `Lucas` 2 1;
(S n) `Lucas` a (S (S b)):
    ! ~Go 1 3 n = ~Go a (S (S b)) Z.
      ~Go a (S (S b)) (S n) = ~Go (S (S b)) c n:
          a `+ (S (S b))` c.



--# binary




--# lists

-- prelude:
--     data Nil;
--     data Cons car cdr;

[]       `RecMap f` [];
[x . xs] `RecMap f` [y . ys]:
    x  `f`     y.
    xs `RecMap f` ys.

xs `Map f`    ys: xs `RevDo (RevMap f)` ys.
xs `RevMap f` ys:
    ! ~Go f xs       [] = ~Go f [] ys.
      ~Go f [x . xs] ys = ~Go f xs [y . ys]:
          x `f` y.

[[x . xs]] `Zip` [[x] . ys]:
    x ~ [x];
    xs `Map ~` ys.
[[x . xs] ys . zs] `Zip` [[x y . zs] . xyzs]:
    [ys . zs] `Zip` yzs.
    ! ~Go [x . xs] yzs        []   = ~Go [] []  xyzs'.
      ~Go [x . xs] [yz . yzs] xyzs = ~Go xs yzs [[x . yz] . xyzs];
    [[x y . zs] . xyzs] `Rev` xyzs'. 

inp `RevDo f` out:
    inp `f`   rout.
    out `Rev` rout.
xs `Rev` ys:
    ! ~Go xs       [] = ~Go [] ys.
      ~Go [x . xs] ys = ~Go xs [x . ys];

(S n) x `Replicate` [x . xs]:
    ! ~Go x n     [] = ~Go x Z xs.
      ~Go x (S n) xs = ~Go x n [x' . xs]:
          `Dup x` x'.

xs n `Split` ys zs:
    xs n `RevSplit` ys' zs.
    ys `Rev` ys'.

xs n `RevSplit` ys zs:
    ! ~Go n [] xs = ~Go Z ys zs.
      ~Go (S n) ys [x . xs] = ~Go n [x . ys] xs;

xs `Break p` ys zs:
    `(~ p) x` b':
        `p x` b.
        b `Not` b'.
    xs `Span (~ p)` ys zs.

xs `Span p` ys zs:
    ys `Rev` ys'.
    ! ~Go p [] xs = ~Go p False ys' zs.
      ~Go p ys [] = ~Go p False ys [];
      ~Go p ys [x . xs] = ~Go p b ys [x . xs]:
          `p x` b.
      ~Go p True ys [x . xs] = ~Go p [x . ys] xs;


--# sorting (mergesort)

`Merge p [] []` [];
`Merge p [x . xs] []` [x' . xs']:
    `Dup [x . xs]` [x' . xs'].
`Merge p [] [y . ys]` [y' . ys']:
    `Dup [y . ys]` [y' . ys'].
`Merge p [x . xs] [y . ys]` [z . zs]:
    `p x y` b.
    `~Merge p b x xs y ys` z zs.

    `~Merge p True x xs y ys` z zs:
        `Dup x` z.
        `Merge p xs [y . ys]` zs.
    `~Merge p False x xs y ys` z zs:
        `Dup y` z.
        `Merge p [x . xs] ys` zs.

[]         `Halve` []       [];
[x]        `Halve` [x]      [];
[x y . zs] `Halve` [x . xs] [y . ys]:
       zs  `Halve`      xs       ys.

-- use Bennett's algorithm to avoid exponential recursion overhead
`MergeSort p xs` ys':
    xs `MergeSortIrrev p` h ys.
    `Dup ys` ys'.

[]         `MergeSortIrrev p` (Garbage False)    [];
[a]        `MergeSortIrrev p` (Garbage True)     [a];
[a b . cs] `MergeSortIrrev p` (Garbage h1 h2 h3) cs':
    cs `Halve` as bs.
    [a . as] `MergeSortIrrev p` h1 as'.
    [b . bs] `MergeSortIrrev p` h2 bs'.
    as' bs' `MergeIrrev p` h3 cs'.

data L;
data R;

xs ys `MergeIrrev p` ds zs':
    ! ~Go p [] xs ys [] = ~Go p ds [] [] zs.
    zs `Rev` zs'.

    ~Go p ds [x . xs] [] zs = ~Go p [L . ds] xs [] [x . zs];
    ~Go p ds [] [y . ys] zs = ~Go p [R . ds] [] ys [y . zs];

    ~Go p ds [x . xs] [y . ys] zs = ~Go p ds b [x . xs] [y . ys] zs:
      `p x y` b.
    ~Go p ds True  [x . xs] [y . ys] zs = ~Go p [L . ds] xs [y . ys] [x . zs];
    ~Go p ds False [x . xs] [y . ys] zs = ~Go p [R . ds] [x . xs] ys [y . zs];


--# sorting (insertion sort)

xs `InsertSort p` ns ys:
    ! ~Go p xs [] [] = ~Go p [] ns ys.
    ~Go p [x . xs] ns ys = ~Go p xs [n . ns] ys':
        x ys `Insert p` n ys'.

[] `InsertSortRec p` [] [];
[x . xs] `InsertSortRec p` [n . ns] zs:
    xs `InsertSortRec p` ns ys.
    x ys `Insert p` n zs.

x [] `Insert p` 0 [x];
x [y . ys] `Insert p` n [z z' . zs]:
    `p x y` b.
    x [y . ys] b `~Insert p` n [z z' . zs].

    x [y . ys] False `~Insert p` (S n) [y . zs]:
        x ys `Insert p` n zs.
    x [y . ys] True `~Insert p` Z [x y . ys];


--# strings

-- ascii

0 `Num=Char` #"'\0"; 1 `Num=Char` #"'\1"; 2 `Num=Char` #"'\2";
3 `Num=Char` #"'\3"; 4 `Num=Char` #"'\4"; 5 `Num=Char` #"'\5";
6 `Num=Char` #"'\6"; 7 `Num=Char` #"'\7"; 8 `Num=Char` #"'\8";
9 `Num=Char` #"'\9"; 10 `Num=Char` #"'\10"; 11 `Num=Char` #"'\11";
12 `Num=Char` #"'\12"; 13 `Num=Char` #"'\13"; 14 `Num=Char` #"'\14";
15 `Num=Char` #"'\15"; 16 `Num=Char` #"'\16"; 17 `Num=Char` #"'\17";
18 `Num=Char` #"'\18"; 19 `Num=Char` #"'\19"; 20 `Num=Char` #"'\20";
21 `Num=Char` #"'\21"; 22 `Num=Char` #"'\22"; 23 `Num=Char` #"'\23";
24 `Num=Char` #"'\24"; 25 `Num=Char` #"'\25"; 26 `Num=Char` #"'\26";
27 `Num=Char` #"'\27"; 28 `Num=Char` #"'\28"; 29 `Num=Char` #"'\29";
30 `Num=Char` #"'\30"; 31 `Num=Char` #"'\31"; 32 `Num=Char` #"'\32";
33 `Num=Char` #"'\33"; 34 `Num=Char` #"'\34"; 35 `Num=Char` #"'\35";
36 `Num=Char` #"'\36"; 37 `Num=Char` #"'\37"; 38 `Num=Char` #"'\38";
39 `Num=Char` #"'\39"; 40 `Num=Char` #"'\40"; 41 `Num=Char` #"'\41";
42 `Num=Char` #"'\42"; 43 `Num=Char` #"'\43"; 44 `Num=Char` #"'\44";
45 `Num=Char` #"'\45"; 46 `Num=Char` #"'\46"; 47 `Num=Char` #"'\47";
48 `Num=Char` #"'\48"; 49 `Num=Char` #"'\49"; 50 `Num=Char` #"'\50";
51 `Num=Char` #"'\51"; 52 `Num=Char` #"'\52"; 53 `Num=Char` #"'\53";
54 `Num=Char` #"'\54"; 55 `Num=Char` #"'\55"; 56 `Num=Char` #"'\56";
57 `Num=Char` #"'\57"; 58 `Num=Char` #"'\58"; 59 `Num=Char` #"'\59";
60 `Num=Char` #"'\60"; 61 `Num=Char` #"'\61"; 62 `Num=Char` #"'\62";
63 `Num=Char` #"'\63"; 64 `Num=Char` #"'\64"; 65 `Num=Char` #"'\65";
66 `Num=Char` #"'\66"; 67 `Num=Char` #"'\67"; 68 `Num=Char` #"'\68";
69 `Num=Char` #"'\69"; 70 `Num=Char` #"'\70"; 71 `Num=Char` #"'\71";
72 `Num=Char` #"'\72"; 73 `Num=Char` #"'\73"; 74 `Num=Char` #"'\74";
75 `Num=Char` #"'\75"; 76 `Num=Char` #"'\76"; 77 `Num=Char` #"'\77";
78 `Num=Char` #"'\78"; 79 `Num=Char` #"'\79"; 80 `Num=Char` #"'\80";
81 `Num=Char` #"'\81"; 82 `Num=Char` #"'\82"; 83 `Num=Char` #"'\83";
84 `Num=Char` #"'\84"; 85 `Num=Char` #"'\85"; 86 `Num=Char` #"'\86";
87 `Num=Char` #"'\87"; 88 `Num=Char` #"'\88"; 89 `Num=Char` #"'\89";
90 `Num=Char` #"'\90"; 91 `Num=Char` #"'\91"; 92 `Num=Char` #"'\92";
93 `Num=Char` #"'\93"; 94 `Num=Char` #"'\94"; 95 `Num=Char` #"'\95";
96 `Num=Char` #"'\96"; 97 `Num=Char` #"'\97"; 98 `Num=Char` #"'\98";
99 `Num=Char` #"'\99"; 100 `Num=Char` #"'\100"; 101 `Num=Char` #"'\101";
102 `Num=Char` #"'\102"; 103 `Num=Char` #"'\103"; 104 `Num=Char` #"'\104";
105 `Num=Char` #"'\105"; 106 `Num=Char` #"'\106"; 107 `Num=Char` #"'\107";
108 `Num=Char` #"'\108"; 109 `Num=Char` #"'\109"; 110 `Num=Char` #"'\110";
111 `Num=Char` #"'\111"; 112 `Num=Char` #"'\112"; 113 `Num=Char` #"'\113";
114 `Num=Char` #"'\114"; 115 `Num=Char` #"'\115"; 116 `Num=Char` #"'\116";
117 `Num=Char` #"'\117"; 118 `Num=Char` #"'\118"; 119 `Num=Char` #"'\119";
120 `Num=Char` #"'\120"; 121 `Num=Char` #"'\121"; 122 `Num=Char` #"'\122";
123 `Num=Char` #"'\123"; 124 `Num=Char` #"'\124"; 125 `Num=Char` #"'\125";
126 `Num=Char` #"'\126"; 127 `Num=Char` #"'\127";

`Char< xc yc` b:
  xn `Num=Char` xc.
  yn `Num=Char` yc.
  `< xn yn` b.


--# computational theory

--## tapes

-- a one-hole context for a bi-infinite tape
data Tape l x r;

  data Symb x;
  data Blank;

  [Blank    x . xs] `Pop` Blank    [x . xs];
  [(Symb x)   . xs] `Pop` (Symb x) xs;
  []                `Pop` Blank    [];

  (Tape l x r) `Left` (Tape l' x' r'):
    l  `Pop` x' l'.
    r' `Pop` x  r.

  t `Right` t':
    t' `Left` t.

  xs `MkTape` (Tape [] Blank xs'):
    x ~ (Symb x);
    xs `Map ~` xs'.

-- reversible turing machine, cf Bennett
    -- the rule
    --  S1 C E / D / / -> B A - F 0 + S2
    -- is mapped to

          S1 (Tape l1 C r1) (Tape l2 E r2) t3  (Tape l4 D r4) t5  t6
        = S2 (Tape l1 B r1) (Tape l2 A r2) t3' (Tape l4 F r4) t5' t6':

            t3 `Left`  t3'.
            t5 `Id`    t5'.
            t6 `Right` t6'.

    -- we also have

        ! Start t1 t2 t3 t4 t5 t6;
        ! Stop  t1 t2 t3 t4 t5 t6;


-- numeric tapes

Blank    `TS=Num` Z;
(Symb n) `TS=Num` (S n);

nums `NumTape` (Tape [] Blank r):
  r `Map TS=Num` nums.

! AlignTape t _; ! _ t dn AlignTape;
  AlignTape (Tape [l . ls] x r) _
= AlignTape (Tape [l . ls] x r) Left 0;

  AlignTape (Tape [] Blank [r . rs]) _
= AlignTape (Tape [] Blank [r . rs]) Right 0;

  AlignTape (Tape [] (Symb x) r) _
= _ (Tape [] Blank [(Symb x) . r]) Null AlignTape;

  AlignTape (Tape [] Blank []) _
= _ (Tape [] Blank []) Null AlignTape;

  AlignTape (Tape [l . ls] x r) Left n
= AlignTape tape'               Left (S n):
    (Tape [l . ls] x r) `Left` tape'.

  AlignTape (Tape [] Blank [r . rs]) Right n
= AlignTape tape'                    Right (S n):
    tape' `Left` (Tape [] Blank [r . rs]).

  AlignTape (Tape [] Blank []) Right n
= _ (Tape [] Blank []) (, ERROR n) AlignTape;

  AlignTape (Tape [] (Symb x) r) d n
= _ (Tape [] Blank [(Symb x) . r]) (, d n) AlignTape;



-- brainf***
-- here we use an unbounded/bignum implementation, with undefined underflow

xs `BFParse` ys:
    ~BFP xs = ~BFP ys' [] False.
    ys `Rev` ys'.

    ! ~BFP xs; ! ~BFP ys rest b;
    ~BFP xs = ~BFP [] xs;

    ~BFP ys ['> . xs]    = ~BFP ['> . ys] xs;
    ~BFP ys ['< . xs]    = ~BFP ['< . ys] xs;
    ~BFP ys ['+ . xs]    = ~BFP ['+ . ys] xs;
    ~BFP ys ['- . xs]    = ~BFP ['- . ys] xs;
    ~BFP ys [#"'." . xs] = ~BFP [#"'." . ys] xs;
    ~BFP ys [', . xs]    = ~BFP [', . ys] xs;

    ~BFP ys [#"'[" . xs] = ~BFP [(, loop) . ys] xs':
        ~~BFP xs = ~~BFP loop xs' True.

    ~BFP ys [#"']" x . rest] = ~BFP ys' [x . rest] True:
        ys `Rev` ys'.

    ~BFP ys [#"']"] = ~BFP ys' [] True:
        ys `Rev` ys'.

    ~BFP ys [] = ~BFP ys [] False;


prog inp nums `BrainF***` outp nums' (Garbage inp' dn h):
    prog `BFParse` instrs.

    nums `NumTape` tape0.
    tape1 `Left` tape0.
    ~BF instrs inp [] tape1 = ~BF [] inp' outp' tape2 h.
    tape2 `AlignTape` tape3 dn.
    nums' `NumTape` tape3.
    outp `Rev` outp'.

    ! ~BF instrs inp outp tape; ! ~BF [] inp outp tape h;
      ~BF instrs inp outp tape = ~BF instrs inp outp tape _;

      ~BF ['> . instrs] inp outp tape  h
    = ~BF instrs        inp outp tape' (, '> h):
        tape' `Left` tape.

      ~BF ['< . instrs] inp outp tape  h
    = ~BF instrs        inp outp tape' (, '< h):
        tape `Left` tape'.

      ~BF ['+ . instrs] inp outp (Tape l x  r) h
    = ~BF instrs        inp outp (Tape l x' r) (, '+ h):
        x `TS=Num` n. x' `TS=Num` (S n).

      ~BF ['- . instrs] inp outp (Tape l (Symb n) r) h
    = ~BF instrs        inp outp (Tape l x  r) (, '- h):
        x `TS=Num` n.

      ~BF ['- . instrs] inp outp (Tape l Blank r) h
    = ~BF instrs        inp outp (Tape l Blank r) (, '-0 h);

      ~BF [#"'." . instrs] inp outp        (Tape l x r) h
    = ~BF instrs           inp [n' . outp] (Tape l x r) (, #"'." h):
        x `TS=Num` n. `Dup n` n'.

      ~BF [', . instrs] [n . inp] outp (Tape l x r) h
    = ~BF instrs        inp       outp (Tape l y r) (, ', x h):
        y `TS=Num` n.

      -- EOF, leave value unchanged
    --   ~BF [', . instrs] [] outp (Tape l x r) h
    -- = ~BF instrs        [] outp (Tape l x r) (, ', h);
      -- EOF, return 0
      ~BF [', . instrs] [] outp (Tape l x r) h
    = ~BF instrs        [] outp (Tape l Blank r) (, ', _ x h);

      ~BF [(, loop) . instrs] inp  outp  (Tape l (Symb x) r) h
    = ~BF [(, loop) . instrs] inp' outp' tape'               (, S h' h):
        `Dup loop` loop'.
          ~~BF loop' inp  outp  (Tape l (Symb x) r)
        = ~~BF []    inp' outp' tape'               h'.

      ~BF [(, loop) . instrs] inp outp (Tape l Blank r) h
    = ~BF instrs              inp outp (Tape l Blank r) (, Z loop h);

prog inp nums `BrainF***Ascii` outp nums' h:
    inp' `Map Num=Char` inp.
    outp' `Map Num=Char` outp.
    prog inp' nums `BrainF***` outp' nums' h.

-- mu recursive functions
data Const n;
data Succ;
data Id i;
data Sub g fs;
data Rec base iter;
data Minim f;

xs `Mu (Const n)` n' (Garbage xs):
    `Dup n` n'.

[x] `Mu Succ` (S x) (Garbage);

xs `Mu (Id i)` y (Garbage ys zs):
    `Dup i` i'.
    xs i' `RevSplit` [y . ys] zs.

xs `Mu (Sub g fs)` z (Garbage xs h hs):
    fs `Map (~Apply xs)` fxhs.
    [fs ys hs] `Zip` fxhs.
    ys `Mu g` z h.

    f `~Apply xs` [f x h]:
        `Dup xs` xs'.
        xs' `Mu f` x h.

[n . xs] `Mu (Rec f g)` y (Garbage n' xs hs):
    `Dup xs` xs'.
    xs' `Mu f` x h.
    ! ~Go n     Z g x xs [h] = ~Go Z n'    g y xs hs.
      ~Go (S n) m g x xs hs  = ~Go n (S m) g y xs [h . hs]:
        `Dup m xs` m' xs'.
        [m' x . xs'] `Mu g` y h.

xs `Mu (Minim f)` i (Garbage xs hs):
    ! ~Go f Z xs (S Z) [] = ~Go f (S i) xs Z hs.
      ~Go f i xs (S n) hs = ~Go f (S i) xs y (, n h hs):
        `Dup i xs` i' xs'.
        [i' . xs'] `Mu f` y h.

--   clean variants
--      these can be used to reduce the amount of space used,
--      but if they are nested then there will be an exponential
--      time overhead in the nesting level...
data Clean f;
--      clean recursion
-- ...
--      clean minimalisation
xs `Mu (Clean (Minim f))` i (Garbage xs):
    ! ~Go f Z xs False = ~Go f i     xs True.
      ~Go f i xs False = ~Go f (S i) xs b:
        [i . xs] `Mu f` y h.
        `~~Fin y` b.
    `~Fin Z`     True.
    `~Fin (S n)` False.