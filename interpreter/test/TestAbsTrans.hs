module TestAbsTrans (tests) where

import Test.HUnit
import qualified Data.ByteString.Lazy.Char8 as BL
import Data.Map as Map
import Data.String (fromString)

import Lang.LAMA.Identifier
import Lang.LAMA.Types
import Lang.LAMA.Typing.TypedStructure
import Lang.LAMA.Parse

tests :: Test
tests = TestList [
    TestLabel "Types" testTypes,
    TestLabel "Constants" testConstants,
    TestLabel "Switch" testSwitchTrans,
    TestLabel "UpDownCounter" testUpDownCounterTrans
  ]

-- Helper
false :: Constant i
false = boolConst False

trueE :: Expr i
trueE = constAtExpr $ boolConst True

varExpr :: i -> Type i -> Expr i
varExpr v t = mkTyped (AtExpr (AtomVar v)) t

intConst :: Integer -> Constant i
intConst c = mkTyped (IntConst c) intT

intE :: Integer -> Expr i
intE = constAtExpr . intConst

intConstE :: Integer -> ConstExpr i
intConstE c = mkTyped (Const $ intConst c) intT

ite :: Expr i -> Expr i -> Expr i -> Expr i
ite c e1 e2 = mkTyped (Ite c e1 e2) boolT

eqE :: Expr i -> Expr i -> Expr i
eqE e1 e2 = mkTyped (Expr2 Equals e1 e2) boolT

leqE :: Expr i -> Expr i -> Expr i
leqE e1 e2 = mkTyped (Expr2 LEq e1 e2) boolT

notE :: Expr i -> Expr i
notE e = mkTyped (LogNot e) boolT

checkEqual :: Program PosIdent -> BL.ByteString -> Test
checkEqual t inp = case parseLAMA inp of
  Left (ParseError pe) -> TestCase $ assertFailure $ "Parsing failed: " ++ show pe
  Left (StaticError se) -> TestCase $ assertFailure $ "Conversion failed: " ++ show se
  Left (TypeError te) -> TestCase $ assertFailure $ "Type check failed: " ++ show te
  Right t' -> t ~=? t'

---------------

typesSrc :: BL.ByteString
typesSrc = BL.pack $ unlines [
  "typedef",
  "  enum e = { e1, e2 };",
  "nodes node main() returns (x : (# e int (# int real) int^5) ) let tel",
  "local x : (# e int (# int real) int^5);",
  "definition x = (use main);" ]

expectedTypes :: Program PosIdent
expectedTypes =
  Program {
    progEnumDefinitions = fromList [
      (e, EnumDef [e1, e2])
    ],
    progConstantDefinitions = fromList [],
    progDecls = Declarations {
      declsNode = Map.fromList [(fromString "main", Node {
        nodeDecls = Declarations Map.empty [] [] [],
        nodeOutputs = [Variable x (ProdType [EnumType e, intT, ProdType [intT, realT], int5])],
        nodeFlow = Flow {flowDefinitions = [], flowTransitions = []},
        nodeAutomata = Map.fromList [], nodeInitial = fromList [], nodeAssertion = trueE
      })],
      declsInput = [],
      declsState = [],
      declsLocal = [Variable x (ProdType [EnumType e, intT, ProdType [intT, realT], int5])]
    },
    progFlow = Flow [NodeUsage x main []] [],
    progAssertion = trueE, progInitial = fromList [], progInvariant = trueE
  }
  where
    main = fromString "main"
    e = fromString "e"
    e1 = EnumCons $ fromString "e1"
    e2 = EnumCons $ fromString "e2"
    x = fromString "x"
    int5 = ProdType $ replicate 5 intT

testTypes :: Test
testTypes = checkEqual expectedTypes typesSrc

---------------

constantsSrc :: BL.ByteString
constantsSrc = BL.pack $ unlines [
  "nodes",
  "  node main() returns (x : sint[32], y : uint[16]) let",
  "    definition",
  "      x = sint[32]((- 5));",
  "      y = uint[16](1322);",
  "tel" ]

expectedConstants :: Program PosIdent
expectedConstants =
  Program {
    progEnumDefinitions = fromList [],
    progConstantDefinitions = fromList [],
    progDecls = Declarations {
      declsNode = Map.fromList [(fromString "main", Node {
        nodeDecls = Declarations Map.empty [] [] [],
        nodeOutputs = [
          Variable x (GroundType (SInt 32)),
          Variable y (GroundType (UInt 16))
        ],
        nodeFlow = Flow [
          InstantExpr x $ constAtExpr $ mkTyped (SIntConst 32 (-5)) (GroundType (SInt 32)),
          InstantExpr y $ constAtExpr $ mkTyped (UIntConst 16 1322) (GroundType (UInt 16))
        ] [],
        nodeAutomata = Map.fromList [], nodeInitial = fromList [], nodeAssertion = trueE
      })],
      declsInput = [],
      declsState = [],
      declsLocal = []
    },
    progFlow = Flow [] [],
    progAssertion = trueE, progInitial = fromList [], progInvariant = trueE
  }
  where
    x = fromString "x"
    y = fromString "y"

testConstants :: Test
testConstants = checkEqual expectedConstants constantsSrc

---------------

switch :: BL.ByteString
switch = BL.pack $ unlines [
    "input on : bool; off : bool;",
    "nodes",
    "node Switch(on : bool, off: bool) returns (so: bool) let",
    "  local",
    "    s_ : bool;",
    "  state",
    "    s : bool;",
    "  definition",
    "    s_ = (ite s (not off) on);",
    "    so = s_;",
    "  transition",
    "    s' = s_;",
    "  initial s = false;",
    "tel",
    "local so : bool;",
    "definition so = (use Switch on off);"]

expectedSwitch :: Program PosIdent
expectedSwitch =
  Program {
    progEnumDefinitions = fromList [],
    progConstantDefinitions = fromList [],
    progDecls = Declarations {
      declsNode = Map.fromList [(fromString "Switch", Node {
        nodeDecls = Declarations {
          declsNode = Map.empty,
          declsInput = [Variable on boolT, Variable off boolT], 
          declsState = [Variable s boolT],
          declsLocal = [Variable s_ boolT]
        },
        nodeOutputs = [Variable so boolT],
        nodeFlow = Flow {
          flowDefinitions = [
            InstantExpr s_ $ (
              ite (varExpr s boolT)
                  (notE (varExpr off boolT))
                  (varExpr on boolT)
            ),
            InstantExpr so $ (varExpr s_ boolT)
          ],
          flowTransitions = [StateTransition s (varExpr s_ boolT)]
        },
        nodeAutomata = Map.fromList [],
        nodeInitial = fromList [(s,(mkTyped (Const false) boolT))],
        nodeAssertion = trueE
      })],
      declsInput = [Variable on boolT, Variable off boolT],
      declsState = [],
      declsLocal = [Variable so boolT]
    },
    progFlow = Flow {
      flowDefinitions = [NodeUsage so switchN [varExpr on boolT, varExpr off boolT]],
      flowTransitions = []
    },
    progAssertion = trueE, progInitial = fromList [], progInvariant = trueE
  }
  where
    on = fromString "on"
    off = fromString "off"
    s = fromString "s"
    so = fromString "so"
    s_ = fromString "s_"
    switchN = fromString "Switch"

testSwitchTrans :: Test
testSwitchTrans = checkEqual expectedSwitch switch

-------------

upDownCounter :: BL.ByteString
upDownCounter = BL.pack $ unlines [
  "nodes",
  "  node main () returns (xo : int) let",
  "    local",
  "      x_ : int;",
  "    state",
  "      x : int;",
  "    definition",
  "      xo = x_;",
  "    transition",
  "      x' = x_;",
  "    ",
  "    automaton let",
 "       location A let",
 "         definition x_ = (+ x 1);",
 "       tel",
 "       location B let",
 "         definition x_ = (- x 1);",
 "       tel",
 "       initial A;",
 "       edge (A, B) : (= x 10);",
 "       edge (B, A) : (= x 0);",
 "       edge (A, A) : (not (= x 10));",
 "       edge (B, B) : (not (= x 0));",
 "     tel",
 "     ",
 "     initial x = (- 1);",
 "  tel",
 "local xo : int;",
 "definition xo = (use main);",
 "invariant (<= xo 10);" ]

expectedUpDownCounter :: Program PosIdent
expectedUpDownCounter =
  Program {
    progEnumDefinitions = fromList [], progConstantDefinitions = fromList [],
    progDecls = Declarations {
      declsNode = Map.fromList [(fromString "main", Node {
        nodeDecls = Declarations {
          declsNode = Map.empty,
          declsInput = [],
          declsState = [Variable x intT],
          declsLocal = [Variable x_ intT]
        },
        nodeOutputs = [Variable xo intT],
        nodeFlow = Flow {
          flowDefinitions = [InstantExpr xo $ (varExpr x_ intT)],
          flowTransitions = [StateTransition x (varExpr x_ intT)]
        },
        nodeAutomata = Map.fromList [ (0, Automaton {
          automLocations = [
            Location sA (Flow {
              flowDefinitions = [InstantExpr x_ $ (mkTyped (Expr2 Plus (varExpr x intT) (intE 1)) (GroundType IntT))],
              flowTransitions = []
            }),
            Location sB (Flow {
              flowDefinitions = [InstantExpr x_ $ (mkTyped (Expr2 Minus (varExpr x intT) (intE 1)) (GroundType IntT))],
              flowTransitions = []
            })
          ],
          automInitial = sA,
          automEdges = [
            Edge sA sB (eqE (varExpr x intT) (intE 10)),
            Edge sB sA (eqE (varExpr x intT) (intE 0)),
            Edge sA sA (notE (eqE (varExpr x intT) (intE 10))),
            Edge sB sB (notE (eqE (varExpr x intT) (intE 0)))
          ],
          automDefaults = Map.empty
        })],
        nodeInitial = fromList [(x, intConstE (-1))],
        nodeAssertion = trueE
      })],
      declsInput = [],
      declsState = [],
      declsLocal = [Variable xo intT]      
    },
    progFlow = Flow {
      flowDefinitions = [NodeUsage xo main []],
      flowTransitions = []
    },
    progInitial = fromList [],
    progAssertion = trueE,
    progInvariant = leqE (varExpr xo intT) (intE 10)
  }
  where
    main = fromString "main"
    x = fromString "x"
    x_ = fromString "x_"
    xo = fromString "xo"
    sA = fromString "A"
    sB = fromString "B"

testUpDownCounterTrans :: Test
testUpDownCounterTrans = checkEqual expectedUpDownCounter upDownCounter

