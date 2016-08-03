import std.stdio;
import std.range;
import std.conv;
import std.string;
import std.algorithm;
import std.array;
import std.digest.sha;
import std.range;
import std.math;

import core.exception;

import pegged.grammar;
import pegged.tester.grammartester;

mixin (grammar (`
StackyLang:

    Program    < Word+
    
    Word       < RawString
               / String
               / Real
               / Integer
               / Bool
               / Symbol
    
    Symbol     <-  ~((! [ \t\n\r]) .)+

    Bool       < "true" / "false"

    String     <- :'\"' ~((!'\"') .)* :'\"'
    RawString  <- :'r\"' ~((!'\"') .)* :'\"'
    
    # Numbers.
    Real       <~ Floating ( ('e' / 'E' ) Integer )?
    Floating   <~ Integer '.' Unsigned
    Unsigned   <~ [0-9]+

    Integer    <~ Sign? Unsigned
    Hexa       <~ [0-9a-fA-F]+
    Sign       <- '-' / '+'
    
    # Space related.
    Spacing    <- :(Comment / " " / "\t" / "\r\n" / "\r" / "\n")*
    
    MultiCmt   <~ "%(" ( (!('{'/'}') .)*   MultiCmt*  Spacing* )* ")%"
    Comment    <- MultiCmt 
                / "%" (! Eol  .)* Eol
    Eol        <- ("\r\n" / "\r" / "\n")
`));

void grammarTest () {
    auto tester = new GrammarTester!(StackyLang, "Program");
    
    tester.assertSimilar (`0`,        `Program -> Word -> Integer`);
    tester.assertSimilar (`1.0`,      `Program -> Word -> Real`);  
    tester.assertSimilar (`"hello"`,  `Program -> Word -> String`);  
    tester.assertSimilar (`r"hello"`, `Program -> Word -> RawString`);  
    tester.assertSimilar (`true`,     `Program -> Word -> Bool`);  
}

/** When a cell has the wrong kind. */
class InvalidCellKind : Exception {
    this (
            string msg,
            string file = __FILE__, 
            size_t line = __LINE__, 
            Throwable next = null)
    {
        super (msg, file, line, next);
    }
}

/** When there is not enough element on the stack. */
class StackUnderflow : Exception {
    this (
            string msg,
            string file = __FILE__, 
            size_t line = __LINE__, 
            Throwable next = null)
    {
        super (msg, file, line, next);
    }
}

/** Represents a procedure.
  They are of two types: 
  - made of words
  - natives: implemented by a D delegate.
 */
class Procedure {
    enum : int {
        Words,
        Native
    }
    /// The type of the native procedure implementation.
    alias NativeType = void delegate (Stacky interp);

    /// Tag to differentiate the union.
    int        kind;

    /// Code made of Words
    Cell []    code;

    /// Native code.
    NativeType native; 

    this (int kind, Cell [] code) {
        this.kind = kind;
        this.code = code;
    }

    this (int kind, NativeType native) {
        this.kind   = kind;
        this.native = native;
    }

    /// Create a procedure from an array of code.
    static Procedure fromCode (Cell [] code) {
        return new Procedure (Words, code); 
    }

    /// Create a procedure from a D delegate.
    static Procedure fromDelegate (NativeType native) {
        return new Procedure (Native, native);
    }

    /// Return a string representation.
    override string toString () {
        switch (kind) {
            case Words:
                return "{proc: code %s}".format (code.to!string);
            case Native:
                return "{proc: native %x}".format (&native);
            default:
                return "{proc: empty}";
        }
    }
    
    /** Test for equality betweeen procedures.
      Compare pointers for native procedures.
      Compare arrays of code for words procedures.
     */
    bool opEquals (ref const Procedure proc) const {
        if (kind != proc.kind) {
            return false;
        }

        if (kind == Native) {
            return &native == &proc.native;
        }

        else if (kind == Words) {
            if (code.length != proc.code.length) {
                return false;
            }

            for (size_t i = 0; i < code.length; ++ i) {
                if (code [i] != proc.code [i]) {
                    return false;
                }
                return true;
            }
        }
        return false;
    }

    /// Comparison operator between two procedures.
    int opCmp (ref const Procedure proc) const {
        if (kind == Words && proc.kind == Native) {
            return 1;
        }
        if (kind == Native && proc.kind == Words) {
            return -1;
        }

        if (kind == Native) {
            if (&native == &proc.native) {
                return 0;
            }
            return &native < &proc.native
                 ? -1
                 :  1;
        }

        else if (kind == Words) {
            Cell cCode  = new Cell (Cell.Array);
            cCode.array = (cast (Cell []) this.code).dup;
            
            Cell cProc  = new Cell (Cell.Proc);
            cProc.array = (cast (Cell []) proc.code).dup;

            if (cCode == cProc) { 
                return 0;
            }
            return cCode < cProc
                 ? -1
                 :  1;
        }
        return 1;
    }
}

/** A cell on the stack.
 */
class Cell {
    enum : int { 
        Integer, 
        Floating,
        String, 
        Symbol,
        Bool,
        Array,
        Dict,
        Proc
    }

    /// Tag to discriminate the union.
    int kind;

    union {
        long            integer;
        double          floating;
        string          text;
        string          symbol;
        bool            boolean;
        Cell []         array;
        Procedure       proc;
        
        /** 
           The key is a computed hash of the cell key, 
           and the value is the [key, value] pair. 
           This fixes a segfault when using Cell [Cell].
         */
        Cell [][string] dict;
    }

    this (int kind) {
        this.kind = kind;
    }

    string kindStr () { 
        switch (kind) {
        case Integer: 
            return "Integer";
        case Floating:
            return "Floating";
        case String: 
            return "String";
        case Symbol:
            return "Symbol";
        case Bool:
            return "Bool";
        case Array:
            return "Array";
        case Dict:
            return "Dict";
        case Proc:
            return "Proc";
        default:
            return "unknown";
        }
    }

    /// Initialization from a long value.
    static Cell fromLong (long val) {
        Cell self = new Cell (Integer);
        self.integer = val;
        return self;
    }

    /// Initialization from a double value.
    static Cell fromDouble (double val) {
        Cell self = new Cell (Floating); 
        self.floating = val;
        return self;
    }
    
    /// Initialization from a string value.
    static Cell fromString (string val) {
        Cell self = new Cell (String); 
        self.text = val;
        return self;
    }

    /// Initialization as a symbol from a string value.
    static Cell symbolNew (string val) {
        Cell self = new Cell (Symbol);
        self.symbol = val;
        return self;
    }
    
    /// Initialization from a boolean value.
    static Cell fromBool (bool val) {
        Cell self = new Cell (Bool);
        self.boolean = val;
        return self;
    }
    
    /// Initialization as an empty array.
    static Cell arrayNew () {
        Cell self = new Cell (Array);
        self.array = [];
        return self;
    }
    
    /// Initialization as a procedure from an array of words.
    static Cell procFromCode (Cell [] array) {
        Cell self = new Cell (Proc);
        self.proc = Procedure.fromCode (array);
        return self;
    }

    /// Initialization as a procedure from a D delegate.
    static Cell procFromNative (Procedure.NativeType native) {
        Cell self = new Cell (Proc);
        self.proc = Procedure.fromDelegate (native);
        return self;
    }

    /** Generic Initialization from a value. Type is inferred.
      
      stringKind tells to process string values either as
      - strings with "string", the default
      - symbols with "symbols" otherwise.
      */
    static Cell from (string stringKind = "string", T) (T val)
    if (is (T : long)
    ||  is (T : double)
    ||  is (T : string)
    ||  is (T : bool)
    ||  is (T : Procedure)
    ||  is (T : Procedure.NativeType))
    {

        static if (is (T type : long)) {
            return Cell.fromLong (val);
        
        } else static if (is (T type : double)) {
            return Cell.fromDouble (val);
        
        } else static if (is (T type : string)) {
            static if (stringKind == "string") {
                return Cell.fromString (val);

            } else {
                return Cell.symbolNew (val);
            }

        } else static if (is (T type : bool)) {
            return Cell.fromBool (val); 

        } else static if (is (T type : Procedure)) {
            Cell self = {
                kind: Proc,
                proc: val
            }; 
            return self;

        } else static if (is (T type : Procedure.NativeType)) {
            return Cell.procFromNative (val); 
            
        } 
    }
    
    /** Generic Initialization from an array. Type is inferred.
      
      stringKind tells to process string values either as
      - strings with "string", the default
      - symbols with "symbols" otherwise.
      */
    static Cell from (string stringKind = "string", T) (T [] array) 
    if (  !is (T [] : string)
    && (   is (T    : long)
       ||  is (T    : double)
       ||  is (T    : string)
       ||  is (T    : bool)
       ||  is (T    : Procedure.NativeType)))
    {
        Cell self = Cell.arrayNew ();

        foreach (val; array) {
            self.array ~= Cell.from!(stringKind, T) (val);
        }

        return self;
    }
    
    
    /** Generic Initialization from an associative array. Type is inferred.
      
      stringKind tells to process string values either as
      - strings with "string", the default
      - symbols with "symbols" otherwise.
      */
    static Cell from (string stringKind = "string", K, V) (V [K] dict) 
    if ((   is (V : long)
        ||  is (V : double)
        ||  is (V : string)
        ||  is (V : bool)
        ||  is (V : Procedure)
        ||  is (V : Procedure.NativeType)
        ||  is (V : long [])
        ||  is (V : double [])
        ||  is (V : string [])
        ||  is (V : bool [])
        ||  is (V : Procedure [])
        ||  is (V : Procedure.NativeType []))
    &&  (   is (K : long)
        ||  is (K : double)
        ||  is (K : string)
        ||  is (K : bool)
        ))
    {
        Cell self = new Cell (Dict); 
        self.dict = null;

        foreach (k, v; dict) {
            Cell key = Cell.from!(stringKind) (k); 
            Cell val = Cell.from!(stringKind) (v);

            self.dict [key.sha1Hash] = [key, val];
        }

        return self;
    }
    
    
    
    static Cell dictNew () {
        Cell self = new Cell (Dict);
        self.dict = null;
        return self;
    }
    
    override string toString () {
        switch (kind) {
            case Integer:
                return integer.to!string ~ "i";
            case Floating:
                return floating.to!string ~ "f";
            case String:
                return "\"" ~ text ~ "\"";
            case Symbol:
                return symbol;
            case Bool:
                return boolean ? "true" : "false";
            case Array:
                return "(%s)".format (
                            array.map!(to!string)
                                 .array
                                 .join (", "));
            case Dict:
                string [] repr;
                
                foreach (k, v; dict) {
                    repr ~= "%s: %s".format (v [0], v [1]);
                }
                
                return "[%s]".format (repr.join (", "));

            case Proc:
                return proc.toString;
            default:
                return "<unknown>";
        }
    }

    /// Equality operator.
    bool opEquals (ref const Cell cell) const {
        if (kind == Integer || kind == Floating) {
            switch (kind) {
                case Integer:
                    if (cell.kind == Integer) {
                        return integer == cell.integer;
                    } 
                    if (cell.kind == Floating) {
                        return integer == cell.floating;
                    }
                    return false;
                
                case Floating:
                    if (cell.kind == Integer) {
                        return floating == cell.integer;
                    } 
                    if (cell.kind == Floating) {
                        return floating == cell.floating;
                    }
                    return false;
                default: 
                    return false;
            }
        }
        
        if (kind != cell.kind) {
            return false;
        }

        switch (kind) {
            case String:
                return text == cell.text;

            case Symbol:
                return symbol == cell.symbol;

            case Bool:
                return boolean == cell.boolean;

            case Array:
                if (array.length != cell.array.length) {
                    return false;
                }
                
                for (size_t i = 0; i < array.length; ++ i) {
                    if (array [i] != cell.array [i]) {
                        return false;
                    }
                }
                return true;

            case Dict:
                if (dict.keys.length != cell.dict.keys.length) {
                    return false;
                }
                for (size_t i = 0; i < dict.values.length; ++ i) {
                    if (dict.values [i][0] != cell.dict.values [i][0]
                    ||  dict.values [i][1] != cell.dict.values [i][1])
                    {
                        return false;
                    }
                }
                return true;
            
            case Proc:
                return proc == cell.proc;
            
            default:
                return false;
        }
    }
    
    /// Comparison operator.
    int opCmp (ref const Cell cell) const {
        if (kind == Integer || kind == Floating) {
            switch (kind) {
                case Integer:
                    if (cell.kind == Integer) {
                        return integer == cell.integer
                             ? 0
                             : integer <  cell.integer ? -1 : 1;
                    } 
                    if (cell.kind == Floating) {
                        return integer == cell.floating
                             ? 0
                             : integer <  cell.floating ? -1 : 1;
                    }
                    return false;
                
                case Floating:
                    if (cell.kind == Integer) {
                        return floating == cell.integer
                             ? 0
                             : floating <  cell.integer ? -1 : 1;
                    } 
                    if (cell.kind == Floating) {
                        return floating == cell.floating
                             ? 0
                             : floating <  cell.floating ? -1 : 1;
                    }
                    return 1;
                default: 
                    return 1;
            }
        }
        
        if (kind != cell.kind) {
            return kind < cell.kind ? -1 : 1;
        }

        switch (kind) {
            case String:
                return text == cell.text
                     ? 0
                     : text <  cell.text ? -1 : 1;

            case Symbol:
                return symbol == cell.symbol
                     ? 0
                     : symbol <  cell.symbol ? -1 : 1;

            case Bool:
                return boolean == cell.boolean
                     ? 0
                     : boolean <  cell.boolean ? -1 : 1;

            case Array:
                if (array.length != cell.array.length) {
                    return array.length < cell.array.length ? -1 : 1;
                }
                
                for (size_t i = 0; i < array.length; ++ i) {
                    int cmp = array [i].opCmp (cell.array [i]);
                    
                    if (cmp != 0) {
                        return cmp;
                    }
                }
                return 0;

            case Dict:
                if (dict.keys.length != cell.dict.keys.length) {
                    return dict.keys.length < cell.dict.keys.length
                         ? -1 : 1;
                }
                for (size_t i = 0; i < dict.values.length; ++ i) {
                    int cmpK = dict.values [i][0]
                                   .opCmp (cell.dict.values [i][0]);
                    int cmpV = dict.values [i][1]
                                   .opCmp (cell.dict.values [i][1]);

                    if (cmpK != 0) {
                        return cmpK;
                    }
                    if (cmpV != 0) {
                        return cmpV;
                    }
                }
                return true;
            
            case Proc:
                return proc.opCmp (cell.proc);
            
            default:
                return 1;
        }
    }

    /// Returns a sha1Hash as a string, used for dictionaries.
    string sha1Hash () {
        return toString.sha1Of.toHexString.dup ;
    }

    
    /// Search a key in a dictionary.
    Cell * lookup (Cell symbol) {
        if (kind != Dict) {
            throw new InvalidCellKind ("lookup: we are not a Dict");
        }

        if (symbol.kind != Symbol) {
            throw new InvalidCellKind ("lookup: we are not given a Symbol");
        }

        Cell []* match = symbol.sha1Hash in dict;

        if (! match) {
            return null;
        }

        return &(*match) [1];
    }

    /// Assign at an index for arrays and dictionaries.
    Cell opIndexAssign (Cell value, Cell symbol) {
        if (kind == Array) {
            if (symbol.kind != Integer) {
                throw new InvalidCellKind (
                    "array index assign: need an integer index.");
            }

            array [symbol.integer] = value;
            return value;
        }

        else if (kind == Dict) {
            dict [symbol.sha1Hash] = [symbol, value];
            return value;
        }

        throw new InvalidCellKind (
            "Expected an Array or a Dict.");
    }

    /// Retrieve value at an index for arrays and dictinaries.
    Cell opIndex (Cell key) {
        if (kind == Array) {
            if (key.kind != Integer) {
                throw new InvalidCellKind (
                    "array index assign: need an integer index.");
            }

            return array [key.integer];
        }

        else if (kind == Dict) {
            return dict [key.sha1Hash][1];
        }
        
        throw new InvalidCellKind (
            "Expected an Array or a Dict.");
    }
    
    /// Convert to floating as needed.
    double floatValue () {
        if (kind != Integer || kind != Floating) {
            throw new InvalidCellKind ("asFloating: Not a Number.");
        }

        if (kind == Integer) {
            return integer.to!double;
        }

        return this.floating;
    }

    /// Evaluate a procedure, given a Stacky interpreter.
    void eval (Stacky stacky) {
        //"Cell.eval in %s".writefln (this);
        if (kind != Proc) {
            throw new InvalidCellKind ("Cell.eval: Not a Proc.");
        }

        if (proc.kind == Procedure.Native) {
            proc.native (stacky);

        } else if (proc.kind == Procedure.Words) {
            stacky.eval (proc.code ~ Cell.from!"symbol" ("exit"));
        }
        //"Cell.eval out %s".writefln (this);
    }

}

void cellTest () {
    Cell anInt    = Cell.fromLong (0);
    assert (anInt.integer == 0);

    Cell aReal    = Cell.fromDouble (0.0); 
    assert (aReal.floating == 0); 

    Cell aString  = Cell.fromString  ("hello");
    assert (aString.text == "hello");

    Cell aBool  = Cell.fromBool  (true);
    assert (aBool.boolean == true);

    Cell anArray = Cell.from (["hello", "world"]);
    assert (anArray.array [0].text == "hello");
    assert (anArray.array [1].text == "world");

    Cell symbols = Cell.from!"symbol" (["hello", "world"]); 
    assert (symbols.array [0].kind == Cell.Symbol);

    Cell dict = Cell.from (["hello": "world"]);

    assert (anInt.toString   == "0i");
    assert (aReal.toString   == "0f");
    assert (aString.toString == `"hello"`);
    assert (aBool.toString   == "true");
    assert (anArray.toString == `("hello", "world")`);

    anInt.writeln; 
    aReal.writeln;
    aString.writeln;
    aBool.writeln;
    anArray.writeln;
    dict.writeln;

    Cell testDict = new Cell (Cell.Dict);
    testDict.dict = null;
    testDict [Cell.from!"symbol" ("toto")] = Cell.from (0);

    assert (testDict [Cell.from!"symbol" ("toto")].integer == 0);
}

Cell [] parse (string input) {
    Cell [] tokens;
    ParseTree tree = StackyLang (input);
    
    ParseTree [] words;

    foreach (program; tree.children) {
        foreach (kid; program.children) {
            foreach (word; kid.children) {
                words ~= word;
            }
        }
    }

    foreach (word; words) {
        switch (word.name) {
            case "StackyLang.RawString": 
                tokens ~= Cell.fromString (word.matches [0]);
                break;
            case "StackyLang.String": 
                tokens ~= Cell.fromString (word.matches [0]);
                break;
            case "StackyLang.Real": 
                tokens ~= Cell.fromDouble (word.matches [0].to!double);
                break;
            case "StackyLang.Integer": 
                tokens ~= Cell.fromLong (word.matches [0].to!long);
                break;
            case "StackyLang.Bool": 
                tokens ~= Cell.fromBool (word.matches [0].to!bool);
                break;
            case "StackyLang.Symbol": 
                tokens ~= Cell.symbolNew (word.matches [0].to!string);
                break;
            default:
                continue;
        }
    }
    return tokens;
}

void parseTest () {
    Cell [] tokens = " 1 2 3 ".parse;
    
    foreach (num; [1L, 2L, 3L]) {
        assert (tokens [num -1].integer == num, 
                "%s != %s".format (tokens [num].integer, num));
    }
}

/// Return the top of the stack.
Cell top (Cell [] stack) {
    if (stack.length < 1) {
        throw new StackUnderflow ("top");
    }
    return stack [$ -1];
}

/// Return the Nth element of the stack. `stack.index (0)` is the top.
Cell index (Cell [] stack, size_t n) {
    if (stack.length < n +1) {
        throw new StackUnderflow ("index");
    }
    return stack [$ -1 -n];
}


/// An Input Range over a stack of arrays of cells.
class ExecutionStack {
    /// Keeps track of the iteration.
    size_t cursor = 0;

    /// The cells to be executed.
    Cell [] stack;

    /// Create a new task. May pass a cursor.
    this (Cell [] stackIn = [], size_t cursor = 0) {
        this.stack  = stackIn;
        this.cursor = cursor;

    }

    /// Duplicate this object.
    ExecutionStack dup () {
        return new ExecutionStack (stack.dup, cursor);
    }

    /// Is this stack empty?
    bool empty () {
        return cursor >= stack.length;
    }

    /// The front of the stack: next element to iterate.
    Cell front () {
        //"    ExecutionStack.front: %s".writefln (stack [min (cursor, $-1)]);
        return stack [min (cursor, $-1)];
    }

    /// Move on to the next element.
    void popFront () {
        //"    ExecutionStack.popFront %s".writefln (front);
        ++ cursor;
    }

    /// Insert the given array for execution.
    ExecutionStack insert (Cell [] array) {
        if (empty) {
            stack  = array;
            cursor = 0;
            return this;
        }
        "    ExecutionStack.insert [%s] ~ %s ~ %s"
            .writefln ([front], array, stack [ cursor +1 .. $]);
        stack = [front] ~ array ~ stack [ ++ cursor .. $];
        cursor = 0;
        //"    ExecutionStack.insert: %s".writefln (stack);
        return this;
    }

    /// Prevents a iteration to the next element of the stack.
    void hold () {
        cursor --;
    }
}

/// A template for math binary operations.
void numberOp (void delegate (long, long) integerOp, 
               void delegate (double, double) floatingOp) (Stacky stacky) 
{
    if (stacky.operands.length < 2) {
        throw new StackUnderflow ("numberOp: not enough arguments.");
    }
    Cell b = stacky.index (1); 
    Cell a = stacky.index (2);
    
    string [] msgs = [];
    
    foreach (i, arg; [a, b]) {
        if (arg.kind != Cell.Integer
        &&  arg.kind != Cell.Floating) {
            msgs ~= "numberOp: argument [%d] is not a number (%s): %s."
                    .format (i, arg.kindStr, arg);
        }
    }


    if (! msgs.empty) {
        throw new InvalidCellKind (msgs.join (" "));
    }
    
    stacky.pop ();
    stacky.pop ();
    
    if (a.kind == Cell.Floating || b.kind == Cell.Floating) {
        floatingOp (a.floatValue, b.floatValue);

    } else { 
        integerOp (a.integer, b.integer);
    }
}

void numberFun (void delegate (long) integerOp, 
                void delegate (double) floatingOp) (Stacky stacky) 
{
    if (stacky.operands.length < 1) {
        throw new StackUnderflow ("numberFun: not enough arguments.");
    }
    Cell num = stacky.index (1); 
    
    string [] msgs = [];
    
    if (num.kind != Cell.Integer
    &&  num.kind != Cell.Floating) {
        msgs ~= "numberFun: argument is not a number (%s): %s."
                .format (num.kindStr, num);
    }

    if (! msgs.empty) {
        throw new InvalidCellKind (msgs.join (" "));
    }

    stacky.pop ();
    
    if (num.kind == Cell.Floating) {
        floatingOp (num.floating);

    } else { 
        integerOp (num.integer);
    }
}


/// A template for math binary operations.
void numBinaryOp (alias binOp) (Stacky stacky) {
    numberOp!(
        (long a, long b) {
            Cell result    = new Cell (Cell.Integer);
            result.integer = binOp (a, b);
            stacky.push (result);
        }, 
        (double a, double b) {
            Cell result     = new Cell (Cell.Floating);
            result.floating = binOp (a, b);
            stacky.push (result);
        }) (stacky);
}
        
void cellBinOp (void delegate (Cell a, Cell b) op) (Stacky stacky) 
{
    if (stacky.operands.length < 2) {
        throw new StackUnderflow ("cellBinOp: not enough arguments.");
    }
    Cell b  = stacky.top;
    Cell a  = stacky.index (2);

    stacky.pop ();
    stacky.pop ();

    op (a, b);
}

void boolBinOp (void delegate (Cell a, Cell b) op) (Stacky stacky) {
    if (stacky.operands.length < 2) {
        throw new StackUnderflow ("and: expected 2 arguments.");
    }
    Cell b = stacky.index (1);
    Cell a = stacky.index (2);

    if (a.kind != Cell.Bool
    &&  b.kind != Cell.Bool) {
        throw new InvalidCellKind (
            "Expected 2 booleans got: %s and %s"
            .format (a.kindStr, b.kindStr));
    }

    stacky.pop ();
    stacky.pop ();

    op (a, b);
};


/** The Stacky interpreter.
 */
class Stacky {
    
    /// Operand stack. The top is the end of the array.
    Cell [] operands;
    
    /// Execution stack: tokens to be interpreted.
    ExecutionStack execution;
    
    /// Dictionary stack.
    Cell [] dicts;

    /// Instruction pointer.
    size_t ip = 0;
    
    /// Returns the top of the operand stack.
    Cell top () {
        return operands [0.. ip].top; 
    }

    /** Returns the element at index n on the operand stack.
      index (1) is the top of the stack.
     */
    Cell index (size_t n) {
        Cell [] slice = operands [0 .. ip];
        
        if (slice.length < n) {
            throw new StackUnderflow ("index: stack too short.");
        }

        return slice [ip - n]; 
    }

    /// Push an element on the operand stack.
    void push (Cell cell) {
        operands ~= cell;
        ip ++;
        `push "%s", ip == %d => %s`.writefln (cell, ip, operands);
    }


    /// Remove the element at the top of the stack.
    void pop () {
        if (operands.length < 1) {
            throw new StackUnderflow ("pop");
        }

        Cell cell = top;
        
        if (operands.length == ip) {
            operands.length -= 1;

        } else { 
            operands 
                =  operands [0     .. ip]
                ~  operands [ip +1 .. $];
        }
        `pop "%s": after %s`.writefln (cell, operands);
        -- ip;
    };

    this () {
        // Create the builtin words.
        dicts ~= builtinWords ();

        // A new dictionary on top of the builtins for user defined words.
        Cell userDict = new Cell (Cell.Dict);
        userDict.dict = null;

        dicts ~= userDict;
        execution = new ExecutionStack;
    }


    /// Create the builtin words.
    Cell builtinWords () {
        Procedure.NativeType [string] procs;
        
        /// Discard all elements on the stack.
        procs ["clear-stack"] = (Stacky stacky) {
            if (stacky.operands.length == stacky.ip) {
                stacky.operands = [];
                stacky.ip = 0;
            }
            if (stacky.operands.length < stacky.ip) {
                stacky.operands = stacky.operands [stacky.ip .. $];
            }
        };

        /// Puts the stack length on top of the stack.
        procs ["stack-length"] = (Stacky stacky) {
            stacky.push (Cell.from (stacky.ip));
        };
        
        /// Removes one element at the top of the stack.
        procs ["pop"] = (Stacky stacky) {
            stacky.pop ();
        };

        procs ["drop"] = procs ["pop"];
        
        /// Duplicate an arbitrary element of the stack.
        procs ["index"] = (Stacky stacky) {
            if (stacky.operands.length < 2) {
                throw new StackUnderflow ("pop");
            }
            Cell n = stacky.operands.top;

            if (n.kind != Cell.Integer) {
                throw new InvalidCellKind (
                        "index: expected an integer got: %s"
                        .format (n.toString));
            }

            Cell nTh = stacky.operands.index (n.integer.to!size_t);
            stacky.operands ~= nTh;
        };

        /// Swaps the two elements at the top of the stack.
        procs ["swap"] = (Stacky stacky) {
            if (stacky.operands.length < 2) {
                throw new StackUnderflow ("swap");
            }
            Cell top    = stacky.top;
            stacky.pop ();
            Cell bottom = stacky.top;
            stacky.pop ();

            stacky.push (top);
            stacky.push (bottom);
        };

        procs ["exch"] = procs ["swap"];

        /// Duplicate the top of the stack.
        procs ["dup"] = (Stacky stacky) {
            if (stacky.operands.length < 1) {
                throw new StackUnderflow ("dup");
            }
            stacky.push (stacky.top); 
        };

        /// Duplicate top n elements
        procs ["copy"] = (Stacky stacky) {
            if (stacky.operands.length < 2) {
                throw new StackUnderflow ("copy");
            }

            Cell n = stacky.operands.top;
            stacky.pop ();
            
            if (n.kind != Cell.Integer) {
                throw new InvalidCellKind (
                        "index: expected an integer got: %s"
                        .format (n.toString));
            }
            
            if (stacky.operands.length < n.integer) {
                throw new StackUnderflow ("copy");
            }
            
            Cell [] items 
                = stacky.operands [stacky.ip - n.integer .. stacky.ip];

            foreach (item; items) {
                stacky.push (item);
            }
        };

        /// Roll n elements
        procs ["rolln"] = (Stacky stacky) {
            if (stacky.operands.length < 2) {
                throw new StackUnderflow ("rolln");
            }

            Cell n = stacky.operands.top;
            stacky.pop ();
            
            if (n.kind != Cell.Integer) {
                throw new InvalidCellKind (
                        "rolln: expected an integer got: %s"
                        .format (n.toString));
            }
            if (stacky.operands [0 .. stacky.ip].length < n.integer) {
                throw new StackUnderflow ("rolln");
            }

            Cell bottom = stacky.operands.index (n.integer); 
            Cell top    = stacky.operands.top;

            stacky.operands [stacky.ip - 1]             = bottom;
            stacky.operands [stacky.ip - 1 - n.integer] = top;
        };

        /// Put a mark on the stack.
        procs ["mark"] = (Stacky stacky) {
            stacky.push (Cell.from!"symbol" ("mark"));
        };

        /// Count how many words are on the stack up to the mark.
        procs ["count-to-mark"] = (Stacky stacky) {
            size_t index = 0; 
            bool found = false;

            foreach_reverse (cell; stacky.operands [0 .. stacky.ip]) {
                if (cell.kind == Cell.Symbol
                &&  cell.symbol == "mark") {
                    found = true;
                    break;
                }
                index ++;
            }

            if (! found) {
                throw new Exception ("cleartomark: mark not found.");
            }

            stacky.push (Cell.from (index));
        };
        
        /// Clear the stack up to the mark.
        procs ["clear-to-mark"] = (Stacky stacky) {
            size_t index = 0; 
            bool found   = false;

            foreach_reverse (cell; stacky.operands) {
                if (cell.kind == Cell.Symbol
                &&  cell.symbol == "mark") {
                    found = true;
                    break;
                }
                index ++;
            }

            if (! found) {
                throw new Exception ("cleartomark: mark not found.");
            }

            stacky.operands.length -= index +1;
            stacky.ip -= index +1;
        };

        /// Prints the stack on stdout.
        procs ["print-stack"] = (Stacky stacky) {
            //"print-stack: to ip : %s".writefln (stacky.operands [0 ..ip]);
            //"print-stack: all   : %s".writefln (stacky.operands);
            string [] vals; 

            foreach (cell; stacky.operands [0 .. ip]) {
                vals ~= cell.toString; 
            }

            vals.join (" ").writeln;
        };

        /// Leave an Array opening mark.
        procs ["("] = (Stacky stacky) {
            stacky.push (Cell.from!"symbol" ("("));
        };

        /// Create an array on the stack.
        procs [")"] = (Stacky stacky) {
            Cell tokens  = new Cell (Cell.Array);
            tokens.array = [];
            
            size_t index = 0; 
            bool found   = false;

            foreach_reverse (cell; stacky.operands [0 .. stacky.ip]) {
                if (cell.kind == Cell.Symbol
                &&  cell.symbol == "(") {
                    found = true;
                    break;
                }
                index ++;
            }
            if (! found) {
                throw new Exception ("Unbalanced array parenthesis");
            }
            
            tokens.array = stacky.operands [stacky.ip - index .. stacky.ip];

            foreach (num; stacky.ip - index .. stacky.ip) {
                stacky.pop ();
            }
            // Remove the openning '('.
            stacky.pop ();

            stacky.push (tokens);
        };
        
        /// Leave a dictionary opening mark.
        procs ["["] = (Stacky stacky) {
            stacky.push (Cell.from!"symbol" ("["));
        };

        /// Create a dictionary on the stack.
        procs ["]"] = (Stacky stacky) {
            size_t index = 0; 
            bool found   = false;

            foreach_reverse (cell; stacky.operands [0 .. stacky.ip]) {
                if (cell.kind == Cell.Symbol
                &&  cell.symbol == "[") {
                    found = true;
                    break;
                }
                index ++;
            }
            if (! found) {
                throw new Exception ("Unbalanced dict '[]' parenthesis");
            }

            Cell [] tokens = stacky.operands [stacky.ip - index .. stacky.ip];

            if (tokens.length % 2 != 0) {
                throw new Exception (
                    "Not enough element to create a Dict.");
            }

            foreach (num; stacky.ip - index .. stacky.ip) {
                stacky.pop ();
            }
            // Remove the openning '['.
            stacky.pop ();
            
            Cell dict = new Cell (Cell.Dict);
            dict.dict = null;
            
            for (size_t i = 0; i < tokens.length; ++ i) {
                Cell key = tokens [i ++]; 
                Cell val = tokens [i];
                
                dict.dict [key.sha1Hash] = [key, val];
            }
            stacky.push (dict);
        };
        
        /// Creates a procedure.
        procs ["{"] = (Stacky stacky) {
            Cell [] code;
            int level = 1;
            
            stacky.execution.popFront;

            foreach (token; stacky.execution) {
                if (token.kind == Cell.Symbol && token.symbol == "{") {
                    level ++;
                }
                if (token.kind == Cell.Symbol && token.symbol == "}") 
                {
                    level --;
                    
                    if (level == 0) {
                        break;
                    }
                }

                code ~= token;
            }

            stacky.push (Cell.procFromCode (code));
        };

        /// Define a symbol in the top dictionary.
        procs ["def"] = (Stacky stacky) {
            if (stacky.operands.length < 2) {
                throw new StackUnderflow ("def: not enough arguments.");
            }
            Cell obj   = stacky.top;
            Cell name  = stacky.index (2);
            
            string msg = "";
            
            if (name.kind != Cell.Symbol) {
                throw new InvalidCellKind (
                    "Invalid 1st argument %s, typed %s: not a symbol."
                    .format (name, name.kindStr));
            }
            stacky.pop ();
            stacky.pop ();

            stacky.dicts.top [name] = obj;
        };

        procs ["not"] = (Stacky stacky) {
            if (stacky.operands.length < 1) {
                throw new StackUnderflow ("not: not enough arguments.");
            }
            Cell obj   = stacky.top;

            if (obj.kind != Cell.Bool) {
                throw new InvalidCellKind (
                    "Argument is not a boolean: %s"
                    .format (obj));
            }
            stacky.pop ();
            stacky.push (Cell.from (! obj.boolean));
        };

        procs ["="] = (Stacky stacky) {
            cellBinOp!((a, b) => stacky.push (Cell.fromBool (a == b))) (stacky);
        };
        
        procs ["cmp"] = (Stacky stacky) {
            cellBinOp!((a, b) => stacky.push (Cell.from (a.opCmp (b)))) (stacky);
        };
        
        procs ["<"] = (Stacky stacky) {
            cellBinOp!((a, b) => stacky.push (Cell.fromBool (a < b))) (stacky);
        };
        procs ["<="] = (Stacky stacky) {
            cellBinOp!((a, b) => stacky.push (Cell.fromBool (a <= b))) (stacky);
        };
        
        procs [">"] = (Stacky stacky) {
            cellBinOp!((a, b) => stacky.push (Cell.fromBool (a > b))) (stacky);
        };
        procs [">="] = (Stacky stacky) {
            cellBinOp!((a, b) => stacky.push (Cell.fromBool (a >= b))) (stacky);
        };
        
        procs ["+"] = (Stacky stacky) {
            numBinaryOp!((a, b) => a + b) (stacky);
        };
        
        procs ["-"] = (Stacky stacky) {
            numBinaryOp!((a, b) => a - b) (stacky);
        };
        
        procs ["*"] = (Stacky stacky) {
            numBinaryOp!((a, b) => a * b) (stacky);
        };
        
        procs ["/"] = (Stacky stacky) {
            numBinaryOp!((a, b) => a / b) (stacky);
        };
        
        procs ["mod"] = (Stacky stacky) {
            numBinaryOp!((a, b) => a % b) (stacky);
        };

        procs ["divmod"] = (Stacky stacky) {
            numberOp!(
                (long a, long b) {
                    stacky.push (Cell.from (a / b));
                    stacky.push (Cell.from (a % b));
                }, 
                (double a, double b) {
                    stacky.push (Cell.from (a/ b));
                    stacky.push (Cell.from (fmod (a, b).to!double));

                }) (stacky);
        };

        procs ["neg"] = (Stacky stacky) {
            if (stacky.operands.length < 1) {
                throw new StackUnderflow ("neg: not enough arguments.");
            }
            Cell num = stacky.index (1); 

            if (num.kind == Cell.Integer) {
                stacky.pop ();
                stacky.push (Cell.from (- num.integer));

            } else if (num.kind == Cell.Floating) {
                stacky.pop ();
                stacky.push (Cell.from (- num.floating));

            } else {
                throw new InvalidCellKind (
                    "Not a number (%s): %s"
                    .format (num.kindStr, num));
            }
        };

        procs ["and"] = (Stacky stacky) {
            boolBinOp!((a, b) {
                    stacky.push (Cell.fromBool (a.boolean && b.boolean));
            }) (stacky);
        };
        procs ["or"] = (Stacky stacky) {
            boolBinOp!((a, b) {
                    stacky.push (Cell.fromBool (a.boolean || b.boolean));
            }) (stacky);
        };
        procs ["xor"] = (Stacky stacky) {
            boolBinOp!((a, b) {
                    stacky.push (Cell.fromBool (a.boolean ^ b.boolean));
            }) (stacky);
        };

        procs ["abs"] = (Stacky stacky) {
            numberFun!(
                (long num) {
                    stacky.pop ();
                    stacky.push (Cell.from (abs (num).to!long));
                }, 
                (double num) {
                    stacky.pop ();
                    stacky.push (Cell.from (abs (num).to!double));
                }) (stacky);
        };
        
        procs ["ceil"] = (Stacky stacky) {
            numberFun!(
                delegate void (long num) {}, 
                (double num) {
                    stacky.pop ();
                    stacky.push (Cell.from (ceil (num).to!double));
                }) (stacky);
        };
        
        procs ["floor"] = (Stacky stacky) {
            numberFun!(
                delegate void (long num) {}, 
                (double num) {
                    stacky.pop ();
                    stacky.push (Cell.from (floor (num).to!double));
                }) (stacky);
        };

        procs ["round"] = (Stacky stacky) {
            numberFun!(
                delegate void (long num) {}, 
                (double num) {
                    stacky.pop ();
                    stacky.push (Cell.from (round (num).to!double));
                }) (stacky);
        };
        
        procs ["sqrt"] = (Stacky stacky) {
            numberFun!(
                (long num) {
                    stacky.push (
                        Cell.from (sqrt (num.to!double).round.to!long));
                }, 
                (double num) {
                    stacky.push (Cell.from (sqrt (num)));

                }) (stacky);
        };

        procs ["to-int"] = (Stacky stacky) {
            numberFun!(
                delegate void (long num) {}, 
                (double num) {
                    stacky.push (Cell.from (round (num).to!long));
                }) (stacky);
        };

        procs ["exp"] = (Stacky stacky) {
            numberFun!(
                (long num) {
                    stacky.push (
                        Cell.from (round (exp (num.to!double).to!long)));
                },
                (double num) {
                    stacky.push (Cell.from (exp (num)));

                }) (stacky);
        };
        
        procs ["log"] = (Stacky stacky) {
            numberFun!(
                (long num) {
                    stacky.push (
                        Cell.from (round (log (num.to!double).to!long)));
                },
                (double num) {
                    stacky.push (Cell.from (log (num)));

                }) (stacky);
        };
        
        procs ["log10"] = (Stacky stacky) {
            numberFun!(
                (long num) {
                    stacky.push (
                        Cell.from (round (log10 (num.to!double).to!long)));
                },
                (double num) {
                    stacky.push (Cell.from (log10 (num)));

                }) (stacky);
        };
        
        procs ["sin"] = (Stacky stacky) {
            numberFun!(
                (long num) {
                    stacky.push (
                        Cell.from (round (sin (num.to!double).to!long)));
                },
                (double num) {
                    stacky.push (Cell.from (sin (num)));

                }) (stacky);
        };
        
        procs ["cos"] = (Stacky stacky) {
            numberFun!(
                (long num) {
                    stacky.push (
                        Cell.from (round (cos (num.to!double).to!long)));
                },
                (double num) {
                    stacky.push (Cell.from (cos (num)));

                }) (stacky);
        };
        
        procs ["cos"] = (Stacky stacky) {
            numberFun!(
                (long num) {
                    stacky.push (
                        Cell.from (round (cos (num.to!double).to!long)));
                },
                (double num) {
                    stacky.push (Cell.from (cos (num)));

                }) (stacky);
        };
        
        procs ["atan"] = (Stacky stacky) {
            numberFun!(
                (long num) {
                    stacky.push (
                        Cell.from (round (atan (num.to!double).to!long)));
                },
                (double num) {
                    stacky.push (Cell.from (atan (num)));

                }) (stacky);
        };


        procs ["length"] = (Stacky stacky) {
            if (operands.length < 1) {
                throw new StackUnderflow ("length: not enough arguments.");
            }

            Cell cell = stacky.top;

            if (cell.kind == Cell.Array) {
                stacky.pop ();
                stacky.push (Cell.from (cell.array.length));
            }
            else if (cell.kind == Cell.Dict) {
                stacky.pop ();
                stacky.push (Cell.from (cell.dict.length));
            }
            else {
                throw new InvalidCellKind ("length: object has no length.");
            }
        };

        procs ["get"] = (Stacky stacky) {
            if (operands.length < 2) {
                throw new StackUnderflow ("get: not enough arguments.");
            }

            Cell index = stacky.index (1);
            Cell cell  = stacky.index (2);

            if (cell.kind == Cell.Array 
            ||  cell.kind == Cell.Dict) {
                stacky.pop ();
                stacky.pop ();
                stacky.push (cell [index]);
            }
            else if (cell.kind == Cell.String) {
                if (index.kind != Cell.Integer) {
                    throw new InvalidCellKind (
                            "get: index is not an integer.");
                }
                stacky.pop ();
                stacky.pop ();
                stacky.push (Cell.from ("" ~ cell.text [index.integer]));
            }
            else {
                throw new InvalidCellKind ("get: object has no length.");
            }
        };

        procs ["put"] = (Stacky stacky) {
            if (operands.length < 3) {
                throw new StackUnderflow ("get: not enough arguments.");
            }

            Cell value = stacky.index (1);
            Cell index = stacky.index (2);
            Cell cell  = stacky.index (3);

            if (cell.kind == Cell.Array || cell.kind == Cell.Dict) {
                stacky.pop ();
                stacky.pop ();
                stacky.pop ();
                cell [index] = value;
            }
            else {
                throw new InvalidCellKind ("length: object has no length.");
            }
        };

        procs ["a-store"] = (Stacky stacky) {
            if (operands.length < 1) {
                throw new StackUnderflow ("a-store: not enough arguments.");
            }
            
            Cell array = stacky.index (1);

            if (array.kind != Cell.Array) {
                throw new InvalidCellKind ("a-store: not an Array.");
            }

            if (ip -1 == 0) {
                return;
            }

            stacky.pop ();
            array.array ~= operands [0.. ip];
        };
        
        procs ["a-load"] = (Stacky stacky) {
            if (operands.length < 1) {
                throw new StackUnderflow ("a-store: not enough arguments.");
            }
            
            Cell array = stacky.index (1);

            if (array.kind != Cell.Array) {
                throw new InvalidCellKind ("a-store: not an Array.");
            }

            if (ip -1 == 0) {
                return;
            }

            stacky.pop ();

            foreach (cell; array.array) {
                stacky.push (cell);
            }
        };

        procs ["array"] = (Stacky stacky) {
            Cell array  = new Cell (Cell.Array);
            array.array = [];
            stacky.push (array);
        };
        procs ["dict"] = (Stacky stacky) {
            Cell dict = new Cell (Cell.Dict);
            dict.dict = null;
            stacky.push (dict);
        };

        procs ["for-all"] = (Stacky stacky) {
            if (operands.length < 2) {
                throw new StackUnderflow ("for-all: not enough arguments.");
            }
            
            Cell cont = stacky.index (2);
            Cell proc = stacky.index (1);

            if (cont.kind != Cell.Array
            &&  cont.kind != Cell.Dict
            &&  cont.kind != Cell.String) 
            {
                throw new InvalidCellKind (
                    "for-all: not iterable: %s" .format (cont));
            }
            
            if (proc.kind != Cell.Proc) {
                throw new InvalidCellKind (
                    "for-all: not a Proc: %s.".format (proc));
            }

            stacky.pop ();
            stacky.pop ();
            stacky.execution.popFront;
            stacky.execution.popFront;
            
            if (cont.kind == Cell.Array) {
                foreach (cell; cont.array) {
                    stacky.push (cell);
                    proc.eval (stacky);    
                }
            }
            else if (cont.kind == Cell.Dict) {
                foreach (sha1, pair; cont.dict) {
                    stacky.push (pair [0]); 
                    stacky.push (pair [1]);
                    proc.eval (stacky);
                }
            }
            else if (cont.kind == Cell.Dict) {
                foreach (c; cont.text) {
                    stacky.push (Cell.from ("" ~ c));
                    proc.eval (stacky);
                }
            }

            // execution.popFront will be called twice:
            // hold the cursor in place.
            stacky.execution.hold ();
        };

        procs ["if"] = (Stacky stacky) {
            if (operands.length < 2) {
                throw new StackUnderflow ("if: not enough arguments.");
            }

            Cell proc = stacky.index (1);
            Cell cond = stacky.index (2);

            if (proc.kind != Cell.Proc) {
                throw new InvalidCellKind (
                    "if: not a Proc: %s.".format (proc));
            }
            if (proc.kind != Cell.Proc) {
                throw new InvalidCellKind (
                    "if: not a Bool: %s.".format (cond));
            }

            stacky.pop ();
            stacky.pop ();

            if (cond.boolean) {
                proc.eval (stacky);
            }
        };
        
        procs ["ifelse"] = (Stacky stacky) {
            if (operands.length < 3) {
                throw new StackUnderflow ("if: not enough arguments.");
            }

            Cell procElse = stacky.index (1);
            Cell procIf   = stacky.index (2);
            Cell cond     = stacky.index (3);

            if (procIf.kind != Cell.Proc) {
                throw new InvalidCellKind (
                    "ifelse (if): not a Proc: %s.".format (procIf));
            }
            if (procElse.kind != Cell.Proc) {
                throw new InvalidCellKind (
                    "ifelse (else): not a Proc: %s.".format (procElse));
            }
            if (cond.kind != Cell.Bool) {
                throw new InvalidCellKind (
                    "if: not a Bool: %s.".format (cond));
            }

            stacky.pop ();
            stacky.pop ();
            stacky.pop ();

            if (cond.boolean) {
                procIf.eval (stacky);
            } else {
                procElse.eval (stacky);
            }
        };

        return Cell.from!("symbol", string, Procedure.NativeType) (procs);
    }

    /// Look up for a symbol in the dictionary stack.
    Cell * lookup (Cell symbol) {
        Cell * match;

        foreach_reverse (dict; dicts) {
            match = dict.lookup (symbol);
            
            if (match) {
                return match;
            }
        }
        return match;
    }

    /** Look up for a symbol in the dictionary stack. The given string is 
      converted to a Cell Symbol.
      */
    Cell * lookup (string symbol) {
        return lookup (Cell.from!"symbol" (symbol));
    }

    /** Evaluate an input string. */
    void eval (string input) {
        //`eval "%s"`.writefln (input);
        eval (parse (input));
    }

    /** Evaluate an input array of cells. */
    void eval (Cell [] tokens) {
        //"%s".writefln ('='.repeat (50));
        //operands [0.. ip].writeln;
        //"%s".writefln ('='.repeat (50));
        
        //"eval %s".writefln (tokens);
        execution.insert (tokens);
        "execution: %s|%s".writefln (
                execution.stack.dup [execution.cursor .. $], 
                execution.dup.cursor);

        foreach (token; execution) {
            "%s".writefln ('-'.repeat (50));
            operands [0.. ip].writeln;
            "%s".writefln ('-'.repeat (50));
            "%s| %s".writefln (execution.cursor, execution.dup);
            "%s".writefln ('.'.repeat (50));
            push (token);
            `eval "%s"`.writefln (token);

            switch (token.kind) {
                case Cell.Integer: 
                case Cell.Floating:
                case Cell.String: 
                case Cell.Bool:
                case Cell.Array:
                case Cell.Dict:
                case Cell.Proc:
                    continue;

                case Cell.Symbol:
                    if (token.symbol == "exit"
                    ||  token.symbol == "break") {
                        //"exiting.".writeln;
                        pop ();
                        execution.popFront ();
                        return;
                    }
                    evalSymbol (token);
                    continue;
                default:
            }
        }
    }

    void evalSymbol (ref Cell op) {
        //`evalSymbol %s`.writefln (op);

        if (op.symbol.startsWith ("/")
        && !op.symbol.startsWith ("//")
        &&  op.symbol.length > 1)
        {
            op.symbol = op.symbol [1..$];
            "/ symbol: %s".writefln (op);
            return;
        }

        bool immediate = false; 

        if (op.symbol.startsWith ("//")
        &&  op.symbol.length > 2)
        {
            immediate = true;
            op.symbol = op.symbol [2..$];
        }
                
        Cell * match = lookup (op);

        if (! match) {
            throw new Exception (
                "Unknown symbol: "
                ~ op.toString);
        }

        if (immediate) {
            "eval symbol: //%s immediate : %s".writefln (op.symbol, *match);
            execution.insert ([*match]);
            return;
        }

        pop ();
        
        if (match.kind == Cell.Proc) {
            if (match.proc.kind == Procedure.Native) {
                match.proc.native (this);

            } else if (match.proc.kind == Procedure.Words) {
                "evalSymbol Code: %s".writefln (match.proc.code.array);
                execution.insert (match.proc.code.array);
            }
        } else {
            push (*match);
        }
    }
}

void stackyTest () {
    Stacky stacky = new Stacky; 

    assert (stacky.operands == []);
    
    //stacky.push (Cell.from (1));
    //stacky.push (Cell.from (2));
    
    //stacky.eval ("1 2 3 print-stack");
    //stacky.eval ("dup print-stack");
    //stacky.eval ("drop swap print-stack");
    //stacky.eval ("2 copy print-stack");
    //stacky.eval ("3 rolln print-stack");
    //stacky.eval (`mark "hello" "world" count-to-mark print-stack`);
    //stacky.eval (`clear-to-mark print-stack`);
    //stacky.eval (`( 1 2 3 ) print-stack`);
    //stacky.eval (`[ "hello" "world" ] print-stack`);
    //stacky.eval (`{ dup dup } print-stack`);
    //stacky.eval (`clear-stack`);
    //stacky.eval (`/2dup { dup dup } def print-stack`);
    //stacky.eval (`1 2 2dup print-stack`);
    //stacky.eval (`clear-stack`);
    //stacky.eval (`1 2 stack-length print-stack`);
    //stacky.eval (`+ print-stack`);
    //stacky.eval (`* print-stack`);
    //stacky.eval (`clear-stack`);
    //stacky.eval (`( 1 2 3 ) { 2 + } for-all print-stack print-stack`);
    stacky.eval (`true { 2 } if print-stack`);
    stacky.eval (`false { 1 } { 2 } ifelse print-stack`);
    stacky.eval (`clear-stack`);
    stacky.eval (`2 2 + 4 =`);
    stacky.eval (`clear-stack`);
    stacky.eval (`( 0 1 2 3 ) 1 get`);
    stacky.eval (`clear-stack`);
    stacky.eval (`"hello" 1 get`);
    stacky.eval (`
        clear-stack

        /all { 
            /proc   swap def 
            /array  swap def
            /status true def
            
            array { 
                proc true = not { 
                    /status false def 
                } if 
            } for-all
            
            status
        } def 
    `);
    stacky.eval (` ( 1 2 3 ) { 5 < } all `);

    "%s".writefln ('*'.repeat (30));
    stacky.operands.writeln;
    stacky.execution.dup.writeln;
}

void main () {
    grammarTest ();
    cellTest ();
    parseTest ();
    stackyTest ();

    //Stacky stacky = new Stacky; 
    //stacky.eval ("1 2 3");
    //stacky.operands.writeln;
}
