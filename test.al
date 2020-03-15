import "lib.al"


! Foo _;
Foo _ = Foo (Rev [1 2 3 4] _);
Foo (_ l Rev) = _ l Foo;
! _ l Foo; 


a b `BFAdd` c h:
    "[->+<]" [] [a b] `BrainF***` [] [c] h.

`BFHello` outp (Garbage nums h):
    "++++++++[>++++[>++>+++>+++>+<<<<-]>+>+>->>+[<]<-]>>.>---.+++++++..+++.>>.<-.<.+++.------.--------.>>+.>++." [] [] `BrainF***Ascii` outp nums h.

inp `BFRot13` outp (Garbage nums h):
    ",[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>++++++++++++++<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>>+++++[<----->-]<<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>++++++++++++++<-[>+<-[>+<-[>+<-[>+<-[>+<-[>++++++++++++++<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>>+++++[<----->-]<<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>+<-[>++++++++++++++<-[>+<-]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]>.[-]<,]" inp [] `BrainF***Ascii` outp nums h.

`BFSelfIntCode` ">>>+[[-]>>[-]++>+>+++++++[<++++>>++<-]++>>+>+>+++++[>++>++++++<<-]+>>>,<++[[>[->>]<[>>]<<-]<[<]<+>>[>]>[<+>-[[<+>-]>]<[[[-]<]++<-[<+++++++++>[<->-]>>]>>]]<<]<]<[[<]>[[>]>>[>>]+[<<]<[<]<+>>-]>[>]+[->>]<<<<[[<<]<[<]+<<[+>+<<-[>-->+<<-[>+<[>>+<<-]]]>[<+>-]<]++>>-->[>]>>[>>]]<<[>>+<[[<]<]>[[<<]<[<]+[-<+>>-[<<+>++>-[<->[<<+>>-]]]<[>+<-]>]>[>]>]>[>>]>>]<<[>>+>>+>>]<<[->>>>>>>>]<<[>.>>>>>>>]<<[>->>>>>]<<[>,>>>]<<[>+>]<<[+<<]<]";

inp `BFSelfInterpret` outp (Garbage nums h):
    `BFSelfIntCode` code.
    code inp [] `BrainF***Ascii` outp nums h.

`BFTest1` outp h: ",[.,]!Alethe" `BFSelfInterpret` outp h.
`BFTest2` outp h: "Alethe, sigma!" `BFRot13` outp h.
`BFTest3` c    h: 721 349 `BFAdd` c h.

-- yo we heard you liked bf interpreters...
`BFTest4` outp (Garbage n nums h):
    `BFSelfIntCode` code.
    inp n `Split` code "!,.!K".
    code inp [] `BrainF***Ascii` outp nums h.

{- for Rec f g:
     (Rec f g) [n . ns] =>
     g n' previous ns
   where n' counts down
-}

`PR+` (Rec (Id 1) (Sub Succ [(Id 2)]));
`PR*` (Rec (Const 0) (Sub add [(Id 2) (Id 3)])):
    `PR+` add.
`PR^` (Sub (Rec (Const 1) (Sub mult [(Id 2) (Id 3)])) [(Id 2) (Id 1)]):
    `PR*` mult.
`PRFac` (Rec (Const 1) (Sub mult [(Id 2) (Sub Succ [(Id 1)])])):
    `PR*` mult.
`PRPred` (Rec (Const 0) (Id 1));
`PR-` (Sub (Rec (Id 1) (Sub pred [(Id 2)])) [(Id 2) (Id 1)]):
    `PRPred` pred.
`PRSign` (Rec (Const 0) (Const 1));
`PRSign'` (Rec (Const 1) (Const 0));
`PR<` (Sub sg [(Sub subt [(Id 2) (Id 1)])]):
    `PRSign` sg.
    `PR-` subt.
`PR>` (Sub sg [subt]):
    `PRSign` sg.
    `PR-` subt.
`PR<=` (Sub cosg [subt]):
    `PRSign'` cosg.
    `PR-` subt.
`PR>=` (Sub cosg [(Sub subt [(Id 2) (Id 1)])]):
    `PRSign'` cosg.
    `PR-` subt.
`PR=` (Sub cosg [(Sub add [lt gt])]):
    `PRSign'` cosg.
    `PR<` lt.
    `PR>` gt.
    `PR+` add.
`PR/=` (Sub sg [(Sub add [lt gt])]):
    `PRSign` sg.
    `PR<` lt.
    `PR>` gt.
    `PR+` add.
`PRSqRt` (Minim (Sub ne [(Id 2) (Sub mult [(Id 1) (Id 1)])])):
    `PR/=` ne.
    `PR*` mult.
`PRQuotient` (Minim (Sub ge [(Id 2) (Sub mult [(Id 3) (Sub Succ [(Id 1)])])])):
    `PR*` mult.
    `PR>=` ge.

data Named x;
xs `Mu (Named x)` y h:
    `x` prog.
    xs `Mu prog` y h.