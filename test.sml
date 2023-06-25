CM.make("$/basis.cm");
CM.make("$/ml-yacc-lib.cm");


use "Environ.sml";
use "Absyn.sml";
use "PlcParserAux.sml";
use "PlcParser.yacc.sig";
use "PlcParser.yacc.sml";
use "PlcLexer.lex.sml";
use "Parse.sml";


Control.Print.printLength := 1000;
Control.Print.printDepth := 1000;
Control.Print.stringDepth := 1000;

open PlcFrontEnd;
use "PlcChecker.sml";
use "PlcInterp.sml";
use "Plc.sml";

val abs = fromFile "tests/t1.plc";
val venv = []
(* val v = run abs; *)
val v = teval abs venv;
venv;