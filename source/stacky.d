import std.stdio;
import std.range;
import std.conv;
import std.string;
import std.algorithm;
import std.array;
import std.digest.sha;
import std.range;
import std.math;
import std.regex;

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
               / Directive
               / Eol
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

    # Directives
    Directive < ~"#file" String
              / ~"#line" Integer
              / ~"#function" String
    
    # Space related.
    Spacing    <- :(Comment / " " / "\t")*
    
    MultiCmt   <~ "%(" ( (!('{'/'}') .)*   MultiCmt*  Spacing* Eol* )* ")%"
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
    
    tester.assertSimilar (
        `#line 13`, 
        `Program -> Word -> Directive -> Integer`);
    tester.assertSimilar (
        `#file "the-file.txt"`, 
        `Program -> Word -> Directive -> String`);
    tester.assertSimilar (
        `#function "the-function"`, 
        `Program -> Word -> Directive -> String`);
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

/** Undefined or unknown (wrong context) symbol. */
class UnknownSymbol : Exception {
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

    union {
        /// Code made of Words
        Cell []    code;

        /// Native code.
        NativeType native; 
    }

    /// The procedure name, if given.
    protected string _name = "";

    /// Return the procedure name
    string name () {
        return _name;
    }

    /// Sets the procedure name; sets the name to the code token for Code kind.
    void name (string val) {
        this._name = val;

        if (kind == Native) {
            return;
        }

        foreach (token; code) {
            token.funcName = _name;
        }
    }


    /// Initialize a Procedure with tokens of code.
    this (int kind, Cell [] code) {
        this.kind = kind;
        this.code = code;
    }

    /// Initialize a Procedure from native code.
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
    override bool opEquals (Object obj) {
        Procedure proc = cast (Procedure) obj;
        
        if (proc is null) {
            return false;
        }

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
    override int opCmp (Object obj) {
        Procedure proc = cast (Procedure) obj;
        
        if (proc is null) {
            return -1;
        }

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
        Proc,
        Except,
        Ptr
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

        Exception       exception;
        void *          ptr;
    }

    /// The filename where this cell is defined.
    string fileName = ""; 
    
    /// The line number within the filename.
    string lineNo   = "";

    /// The function name in which this cell is.
    string funcName = "";

    /// Changes the fileName field.
    Cell withFileName (string nm) {
        this.fileName = nm;
        return this;
    }

    /// Changes the lineNo field.
    Cell withLineNo (string ln) {
        this.lineNo = ln.strip;
        return this;
    }
    /// Changes the lineNo field.
    Cell withLineNo (size_t ln) {
        this.lineNo = ln.to!string;
        return this;
    }

    /// Changes the funcName field.
    Cell withFuncName (string fn) {
        this.funcName = fn;
        return this;
    }

    /// Simple initialization with just the kind.
    this (int kind) {
        this.kind = kind;
    }

    /// Returns a string representation of the cell's kind.
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
        case Except: 
            return "Exception";
        case Ptr:
            return "Ptr";
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

    alias fromSymbol = symbolNew;
    
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

    /// Initialization from an exception.
    static Cell fromException (Exception exc) {
        Cell self = new Cell (Except);
        self.exception = exc;
        return self;
    }
    
    /// An initialization from a pointer.
    static Cell fromPtr (void * ptr) {
        Cell self = new Cell (Ptr);
        self.ptr = ptr;
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
    ||  is (T : Exception)
    ||  is (T : void *)
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
            
        } else static if (is (T type : Exception)) {
            return Cell.fromException (val);

        } else static if (is (T type : void *)) {
            return Cell.fromPtr (val);
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
       ||  is (T    : Exception)
       ||  is (T    : void *)
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
        ||  is (V : Exception)
        ||  is (V : void *)
        ||  is (V : long [])
        ||  is (V : double [])
        ||  is (V : string [])
        ||  is (V : bool [])
        ||  is (V : Exception [])
        ||  is (V : void * [])
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
    
    
    /// Create a new empty dictionary cell.
    static Cell dictNew () {
        Cell self = new Cell (Dict);
        self.dict = null;
        return self;
    }
    
    /// Return a string representation.
    override string toString () {
        switch (kind) {
            case Integer:
                return integer.to!string ~ "i";
            case Floating:
                return floating.to!string ~ "f";
            case String:
                return "\"" ~ text ~ "\"";
            case Symbol:
                if (symbol.startsWith ("/")
                &&  symbol.length > 1) {
                    return symbol [1..$];
                } 
                else if (symbol.startsWith ("//")
                &&      symbol.length > 2) {
                    return symbol [2..$];
                } 
                else {
                    return symbol;
                }
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

            case Except:
                return "Exception(%s, %s, %s)"
                        .format (exception.msg, 
                                 exception.file,
                                 exception.line);
            case Ptr:
                return "Ptr(%x)".format (ptr);

            default:
                return "<unknown>";
        }
    }

    /// Equality operator.
    override bool opEquals (Object obj) {
        Cell cell = cast (Cell) obj;
        
        if (cell is null) {
            return false;
        }
        
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

            case Except:
                return exception == cell.exception;

            case Ptr:
                return ptr == cell.ptr;
            
            default:
                return false;
        }
    }
    
    /// Comparison operator.
    override int opCmp (Object obj) {
        Cell cell = cast (Cell) obj;
        
        if (cell is null) {
            return -1;
        }

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
            
            case Except:
                return exception == cell.exception
                     ? 0
                     : exception.msg < cell.exception.msg ? -1 : 1;

            case Ptr:
                return ptr == cell.ptr
                     ? 0 
                     : ptr < cell.ptr ? -1 : 1;
            
            default:
                return 1;
        }
    }

    /// Returns a sha1Hash as a string, used for dictionaries.
    string sha1Hash () {
        return toString.sha1Of.toHexString.dup ;
    }

    
    /** Search a key in a dictionary.
     * Returns null if nothing is found.
     *
     * Use a `Cell *` pointer from when Cell was a struct and as such we could
     * not have null values.
     */
    Cell * lookup (Cell symbol) {
        if (kind != Dict) {
            throw new InvalidCellKind ("lookup: we are not a Dict");
        }

        Cell []* match = symbol.sha1Hash in dict;

        if (! match) {
            return null;
        }

        return &(*match) [1];
    }
    
    /// Either return the key at given symbol or return the given alternative.
    Cell lookup (Cell symbol, Cell alt) {
        if (kind != Dict) {
            throw new InvalidCellKind ("lookup: we are not a Dict");
        }

        Cell []* match = symbol.sha1Hash in dict;

        if (! match) {
            return alt;
        }

        return (*match) [1];
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

    /// Retrieve value at an index for arrays and dictionaries.
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
        if (kind != Integer && kind != Floating) {
            throw new InvalidCellKind (
                "asFloating: Not a Number (%s): %s."
                .format (kindStr, this));
        }

        if (kind == Integer) {
            return integer.to!double;
        }

        return this.floating;
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

    Cell testDict = new Cell (Cell.Dict);
    testDict.dict = null;
    testDict [Cell.from!"symbol" ("toto")] = Cell.from (0);

    assert (testDict [Cell.from!"symbol" ("toto")].integer == 0);
}


/** Returns an array of Cell from an input string. */
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

    size_t lineCount = 1;
    string fileName;
    string funcName;
    string lineNumr;

    foreach (word; words) {
        switch (word.name) {
            case "StackyLang.RawString": 
                tokens ~= Cell.fromString (word.matches [0])
                              .withFileName (fileName)
                              .withFuncName (funcName)
                              .withLineNo   (lineCount);
                break;
            case "StackyLang.String": 
                tokens ~= Cell.fromString (word.matches [0])
                              .withFileName (fileName)
                              .withFuncName (funcName)
                              .withLineNo   (lineCount);
                break;
            case "StackyLang.Real": 
                tokens ~= Cell.fromDouble (word.matches [0].to!double)
                              .withFileName (fileName)
                              .withFuncName (funcName)
                              .withLineNo   (lineCount);
                break;
            case "StackyLang.Integer": 
                tokens ~= Cell.fromLong (word.matches [0].to!long)
                              .withFileName (fileName)
                              .withFuncName (funcName)
                              .withLineNo   (lineCount);
                break;
            case "StackyLang.Bool": 
                tokens ~= Cell.fromBool (word.matches [0].to!bool)
                              .withFileName (fileName)
                              .withFuncName (funcName)
                              .withLineNo   (lineCount);
                break;
            case "StackyLang.Symbol": 
                tokens ~= Cell.symbolNew (word.matches [0].to!string)
                              .withFileName (fileName)
                              .withFuncName (funcName)
                              .withLineNo   (lineCount);
                break;
            case "StackyLang.Directive":
                if ("#file" == word.matches [0]) {
                    fileName = word.matches [1];
                } else 
                if ("#line" == word.matches [0]) {
                    lineCount = (word.matches [1].to!size_t) -1;
                } else 
                if ("#function" == word.matches [0]) {
                    funcName = word.matches [1];
                }
                break;
            case "StackyLang.Eol":
                lineCount ++;
                break;

            default:
                continue;
        }
    }
    return tokens;
}

void parseTest () {
    Cell [] tokens = " 1 2 3 ".parse;
    
    assert (tokens == map!(Cell.from) ([1L, 2L, 3L]).array); 

    tokens = `
        clear-stack
        #file "<stdin>" #line 1
        "hello, world!" 
        writeln;
        `.parse;

    assert (tokens [0].fileName == "");
    assert (tokens [0].funcName == "");
    assert (tokens [0].lineNo   == "2");

    assert (tokens [1].fileName == "<stdin>");
    assert (tokens [1].lineNo   == "1");

    assert (tokens [2].lineNo   == "2");
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

/** A stack of cell. 
 * Typically, the code of a procedure being called that is put on top of 
 * the interpreter's execution stack.
 */
class CellStack {
    /// Keeps track of the iteration.
    size_t cursor = 0;

    /// The name of the procedure being executed.
    string procName = ""; 

    /// The cells to be executed.
    Cell [] stack;

    /// Create a new task. May pass a cursor.
    this (Cell [] stackIn = [], size_t cursor = 0, string procName = "") {
        this.stack      = stackIn;
        this.cursor     = cursor;
        this.procName   = procName;
    }

    /// Duplicate this object.
    CellStack dup () {
        return new CellStack (stack.dup, cursor);
    }

    /// Is this stack empty?
    bool empty () {
        return cursor >= stack.length;
    }

    /// The front of the stack: next element to iterate.
    Cell front () {
        /* Return the token and also increase the cursor. */
        return stack [min (cursor ++, $-1)];
    }

    /// Move on to the next element.
    void popFront () {
        /** Actually don't do anything here:
          once we gave a token, it's over, we move on to the next immediately.
         */
    }

    /// String representation of what remains to be executed.
    override string toString () {
        return stack [min (cursor, $ -1)].to!string;
    }
}

/// An Input Range over a stack of arrays of cells.
class ExecutionStack {
    /// The cells to be executed.
    CellStack [] stack;

    /// Create a new task. May pass a cursor.
    this (CellStack [] stackIn = []) {
        this.stack  = stackIn;
    }

    /// Duplicate this object.
    ExecutionStack dup () {
        auto clone = new ExecutionStack; 
        
        for (size_t i = 0; i < stack.length; ++ i) {
            clone.stack ~= stack [i].dup;
        }
        return clone;
    }

    /// Replace our stack with the other's.
    void restoreFrom (ExecutionStack other) {
        this.stack = other.stack;
    }

    /// String representation of what remains to be executed.
    override string toString () {
        string [] res = []; 
        
        for (size_t i = 0; i < stack.length; ++ i) {
            res ~= "[" ~ stack [i].toString () ~ "]";
        }
        return res.join (", ");
    }

    /// Is this stack empty?
    bool empty () {
        if (stack.empty) {
            return true;
        }
        if (stack.length == 1) {
            return stack.back.empty;
        }
        if (stack.length >= 2) {
            for (size_t i = stack.length -1; i >= 0; -- i) {
                if (! stack [i].empty) {
                    return false;
                }
            }
            return true;
        }
        return false;
    }

    /// The front of the stack: next element to iterate.
    Cell front () {
        /* Return the token and also increase the cursor. */
        Cell value = stack.back.front;
        
        if (stack.back.empty) {
            stack.popBack;
        }
        return value;
    }

    /// Move on to the next element.
    void popFront () {
        /** Actually don't do anything here:
          once we gave a token, it's over, we move on to the next immediately.
         */
    }

    /// Insert the given array for execution.
    ExecutionStack insert (Cell [] array, string procName = "") {
        if (procName == "" && ! array.empty) {
            if (array [0].funcName != "") {
                procName = array [0].funcName;
            }
        }
        stack ~= new CellStack (array, 0, procName);
        return this;
    }

    /** Returns from a named procedure.
     * If a named procedure is found in the CellStack array, we pop all the 
     * other CellStack instances on top to get back to the execution
     * just after that named procedure was called.
     */
    void return_ () {
        size_t index;
        string procName = "";

        for (index = 0; index < stack.length; ++ index) {
            if (stack [index].procName != "") {
                break;
            }
        }

        if (procName == "") {
            return;
        }

        stack = stack [0 .. index];
    }

    /// Return stack trace and eventual exception handler.
    Cell trace () {
        if (stack.empty) {
            auto sTrace  = new Cell (Cell.Array);
            sTrace.array = [];

            return sTrace;
        }

        Cell callStack  = new Cell (Cell.Array);
        callStack.array = [];
        
        for (size_t index = 0; index < stack.length; ++ index) {
            if (stack [index].procName == "") {
                continue;
            }
            auto cStack = stack [index];
            Cell token  = cStack.stack [min (cStack.cursor -1, $)];

            Cell trace 
                = Cell.from!"symbol" ([
                    "file": token.fileName,
                    "line": token.lineNo,
                    "func": token.funcName ]);
            trace [Cell.fromSymbol ("token")] = token;

            callStack.array ~= trace;
        }

        return callStack;
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

/// A template for binary functions on numbers.
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
        
/// A template for binary procedures.
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

/// A template for binary boolean operations.
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

    /// Instruction pointer of the operand stack.
    size_t ip = 0;

    /// A flag to stop the interpreter.
    protected bool exitNow = false;

    /** True if the exception handler can deal with an exception, 
        false otherwise. */
    protected bool excManaged = false;

    /// Get to know the call depth to deal with exception handling.
    protected size_t callDepth = 0;
    
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
                    "def: Invalid 1st argument %s, typed %s: not a symbol."
                    .format (name, name.kindStr));
            }
            stacky.pop ();
            stacky.pop ();
            
            Cell key;

            if (name.symbol.startsWith ("/")
            && !name.symbol.startsWith ("//")
            &&  name.symbol.length > 1) 
            {
                key = Cell.fromSymbol (name.symbol [1..$]);
            
            } else {
                key = name;
            }

            if (obj.kind == Cell.Proc) {
                obj.proc.name = key.symbol;
            }

            stacky.dicts.top [key] = obj;
        };

        /// Boolean negation.
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

        /// Comparison operators.
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
        
        /// Arithmetic and maths operators.
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
            numBinaryOp!((a, b) { 
                if (b == 0) {
                    throw new Exception ("Division by zero");
                }
                return a / b;
            }) (stacky);
        };
        
        procs ["mod"] = (Stacky stacky) {
            numBinaryOp!((a, b) { 
                if (b == 0) {
                    throw new Exception ("Division by zero");
                }
                return a % b;
            }) (stacky);
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
        
        /// Boolean logic.
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


        /// Get the length of an Array or Dict.
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

        /// Get the value at the given index in an Array or Dict.
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

        /// Put a value at an index in an Array or Dict.
        procs ["put"] = (Stacky stacky) {
            if (operands.length < 3) {
                throw new StackUnderflow ("put: not enough arguments.");
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
                throw new InvalidCellKind ("put: object has no length.");
            }
        };
        

        /// Append a value to the end of an Array.
        procs ["push"] = (Stacky stacky) {
            if (operands.length < 2) {
                throw new StackUnderflow (
                    "push: not enough arguments: needs 2.");
            }

            Cell array = stacky.index (1);
            Cell value = stacky.index (2);

            if (array.kind == Cell.Array) {
                stacky.pop ();
                stacky.pop ();
                array.array ~= value;
            }
            else {
                throw new InvalidCellKind (
                    "push: Not an array (%s): %s."
                    .format (array.kindStr, array));
            }
        };

        /// Store the stack inside an array.
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
        
        /// Load an array onto the stack.
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

        /// Push a dictionary on the dictionary stack.
        procs ["begin"] = (Stacky stacky) {
            if (operands.length < 1) {
                throw new StackUnderflow (
                    "begin: not enough arguments; needs one.");
            }

            Cell dict = stacky.operands.top;
            stacky.pop ();
            stacky.dicts ~= dict;
        };
        
        /// Pop a dictionary of the dictionary stack.
        procs ["end"] = (Stacky stacky) {
            if (stacky.dicts.length <= 2) {
                /** keep the builtin and user dictionaries*/
                return;
            }

            stacky.dicts.popBack ();
        };


        /// True if a key is contained in a dictionary.
        procs ["known"] = (Stacky stacky) {
            if (operands.length < 2) {
                throw new StackUnderflow ("known: not enough arguments.");
            }
            
            Cell cell = stacky.top ();
            Cell symb = stacky.index (2);

            if (cell.kind != Cell.Dict) {
                throw new InvalidCellKind (
                    "known: expected a Dict, got (%s): %s" 
                    .format (cell.kindStr, cell));
            }
            stacky.pop ();
            stacky.pop ();

            if (auto found = symb.sha1Hash in cell.dict) {
                stacky.push (Cell.fromBool (true));
            
            } else {
                stacky.push (Cell.fromBool (false));
            }
        };
        
        /// Update the topmost dict with a new value for the given key.
        procs ["store"] = (Stacky stacky) {
            if (operands.length < 2) {
                throw new StackUnderflow ("store: not enough arguments.");
            }
            
            Cell value = stacky.top ();
            Cell key   = stacky.index (2);

            stacky.pop ();
            stacky.pop ();

            if (auto found = key.sha1Hash in stacky.dicts.back.dict) {
                (*found) [1] = value;
            }
        };

        /// Remove a key from a dictionary.
        procs ["undef"] = (Stacky stacky) {
            if (operands.length < 2) {
                throw new StackUnderflow ("undef: not enough arguments.");
            }
            
            Cell value = stacky.top ();
            Cell dict  = stacky.index (2);

            if (dict.kind != Cell.Dict) {
                throw new InvalidCellKind (
                    "undef: Expected a dict, got (%s): %s"
                    .format (dict.kindStr, dict));
            }
            stacky.pop ();
            stacky.pop ();

            dict.dict.remove (value.sha1Hash);
        };

        /// Return the dictionary with our stack where the key is defined.
        procs ["where"] = (Stacky stacky) {
            if (operands.length < 1) {
                throw new StackUnderflow ("where: not enough arguments.");
            }
            
            Cell value = stacky.top ();
            stacky.pop ();
            Cell * match;

            foreach_reverse (dict; dicts) {
                match = dict.lookup (value);
                
                if (match) {
                    stacky.push (dict);
                    stacky.push (Cell.fromBool (true));
                    return;
                }
            }
            stacky.push (Cell.fromBool (false));
        };

        /// Create a new empty array.
        procs ["array"] = (Stacky stacky) {
            Cell array  = new Cell (Cell.Array);
            array.array = [];
            stacky.push (array);
        };
        
        /// Create a new empty dict.
        procs ["dict"] = (Stacky stacky) {
            Cell dict = new Cell (Cell.Dict);
            dict.dict = null;
            stacky.push (dict);
        };

        procs ["()"] = procs ["array"];
        procs ["[]"] = procs ["dict"];

        /// Apply a procedure to all the element of an array, dict or string.
        /// For dict, pushes key and value onto the stack for the procedure.
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
            
            if (cont.kind == Cell.Array) {
                foreach (cell; cont.array) {
                    stacky.push (cell);
                    stacky.evalNested (proc);
                }
            }
            else if (cont.kind == Cell.Dict) {
                foreach (sha1, pair; cont.dict) {
                    stacky.push (pair [0]); 
                    stacky.push (pair [1]);
                    stacky.evalNested (proc);
                }
            }
            else if (cont.kind == Cell.Dict) {
                foreach (c; cont.text) {
                    stacky.push (Cell.from ("" ~ c));
                    stacky.evalNested (proc);
                }
            }
        };


        /// Single conditional.
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
                stacky.evalNested (proc);
            }
        };
        
        /// Conditional with alternative.
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
                stacky.evalNested (procIf);
            } else {
                stacky.evalNested (procElse);
            }
        };

        procs ["if-else"] = procs ["ifelse"];

        /// Return from a named procedure.
        procs ["return"] = (Stacky stacky) {
            stacky.execution.return_ ();
        };

        procs ["for"] = (Stacky stacky) {
            if (operands.length < 4) {
                throw new StackUnderflow ("for: not enough arguments.");
            }

            Cell proc   = stacky.index (1);
            Cell limit  = stacky.index (2);
            Cell incr   = stacky.index (3);
            Cell start  = stacky.index (4);

            if (proc.kind != Cell.Proc) {
                throw new InvalidCellKind (
                    "for, proc: not a Proc: %s.".format (proc));
            }
            if (limit.kind != Cell.Integer) {
                throw new InvalidCellKind (
                    "for, limit: not an Integer: %s.".format (limit));
            }
            if (incr.kind != Cell.Integer) {
                throw new InvalidCellKind (
                    "for, incr: not an Integer: %s.".format (incr));
            }
            if (start.kind != Cell.Integer) {
                throw new InvalidCellKind (
                    "for, start: not an Integer: %s.".format (start));
            }

            stacky.pop ();
            stacky.pop ();
            stacky.pop ();
            stacky.pop ();

            if (start <= limit) {
                for (size_t i = start.integer
                    ; i < limit.integer
                    ; i += incr.integer) 
                {
                    stacky.push (Cell.from (i));
                    stacky.evalNested (proc);
                }
            } else {
                for (size_t i = start.integer
                    ; i > limit.integer
                    ; i -= incr.integer) 
                {
                    stacky.push (Cell.from (i));
                    stacky.evalNested (proc);
                }
            }
        };
        
        procs ["repeat"] = (Stacky stacky) {
            if (operands.length < 2) {
                throw new StackUnderflow ("repeat: not enough arguments.");
            }

            Cell proc   = stacky.index (1);
            Cell times  = stacky.index (2);

            if (proc.kind != Cell.Proc) {
                throw new InvalidCellKind (
                    "repeat, proc: not a Proc: %s.".format (proc));
            }
            if (times.kind != Cell.Integer) {
                throw new InvalidCellKind (
                    "repeat, times: not an Integer: %s.".format (times));
            }

            foreach (n; 0 .. times.integer) {
                stacky.evalNested (proc);
            }
        };
        
        procs ["loop"] = (Stacky stacky) {
            if (operands.length < 1) {
                throw new StackUnderflow ("loop: not enough arguments.");
            }

            Cell proc   = stacky.index (1);
            Cell times  = stacky.index (2);

            if (proc.kind != Cell.Proc) {
                throw new InvalidCellKind (
                    "loop, proc: not a Proc: %s.".format (proc));
            }

            for (;;) {
                stacky.evalNested (proc);
            }
        };

        procs ["cond"] = (Stacky stacky) {
            if (operands.length < 1) {
                throw new StackUnderflow ("cond: not enough arguments.");
            }

            Cell conds  = stacky.top ();
            stacky.pop ();

            if (conds.kind != Cell.Array) {
                throw new InvalidCellKind (
                    "cond: not an Array: %s.".format (conds));
            }

            if (conds.array.length % 2 != 0) {
                throw new InvalidCellKind (
                    "cond: array length is not a multiple of 2: %s."
                    .format (conds));
            }
            
            for (size_t i = 0; i < conds.array.length; ++ i) {
                Cell action  = conds.array [i];

                if (action.kind != Cell.Proc
                &&  (action.kind == Cell.Symbol && action.symbol != "/else")) {
                    throw new InvalidCellKind (
                        "cond: array [%s] is not a Proc nor '/else' %s."
                        .format (i, action));
                }
            }

            for (size_t i = 0; i < conds.array.length; ++ i) {
                Cell test   = conds.array [i]; 
                Cell action = conds.array [++ i];
                
                if (test.kind == Cell.Symbol && test.symbol == "/else") {
                    stacky.evalNested (action);
                    return;
                }
                stacky.evalNested (test);

                if (operands.length > 0 
                && stacky.top == Cell.fromBool (true)) {
                    stacky.pop ();
                    stacky.evalNested (action);
                    return;
                }
                stacky.pop ();
            }
        };

        procs ["try-catch"] = (Stacky stacky) {
            if (operands.length < 2) {
                throw new StackUnderflow (
                    "try-catch: not enough arguments (needs 2).");
            }

            Cell recover  = stacky.top ();
            Cell attempt  = stacky.index (2);
            
            if (attempt.kind != Cell.Proc) {
                throw new InvalidCellKind (
                    "try-catch 1st arg is not a Proc: %s.".format (attempt));
            }

            if (recover.kind != Cell.Array) {
                throw new InvalidCellKind (
                    "try-catch: 2nd arg is not an Array: %s.".format (recover));
            }

            if (recover.array.length % 2 != 0) {
                throw new InvalidCellKind (
                    "try-catch, 2nd arg: array length is not a multiple of 2: %s."
                    .format (recover));
            }
            
            stacky.pop ();
            stacky.pop ();
            
            for (size_t i = 0; i < recover.array.length; i += 2) {
                Cell excName  = recover.array [i];
                Cell action   = recover.array [i +1];

                if (excName.kind != Cell.Symbol) {
                    throw new InvalidCellKind (
                        "try-catch, 2nd arg: array [%s] is not a Symbol: %s"
                        .format (i, excName));
                }

                if (action.kind != Cell.Proc) {
                    throw new InvalidCellKind (
                        "try-catch, 2nd arg: array [%s] is not a Proc: %s."
                        .format (i +1, action));
                }
            }
            
            Cell handler = Cell.from ((Stacky stacky) {
                Cell exc       = stacky.top;
                auto coreRe    = regex (`^(core.Exception|object|stacky)\.`);
                auto eName     = typeid (exc.exception)
                                 .to!string
                                 .replaceFirst (coreRe, "");

                for (size_t i = 0; i < recover.array.length; i += 2) {
                    Cell excName  = recover.array [i];
                    Cell action   = recover.array [i +1];

                    if (eName != excName.toString
                    && excName.symbol != "/Exception") 
                    {
                        continue;
                    }
                    
                    stacky.evalNested (action);
                    stacky.excManaged = true;
                    return;
                }
                    
                stacky.excManaged = false;
            });
            
            stacky.evalNested (attempt, handler);
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
    void eval (string input, string procName = "") {
        this.exitNow = false;
        eval (parse (input), procName);
    }

    /** Evaluate an input array of cells. */
    void eval (Cell [] tokens, string procName = "") {
        
        execution.insert (tokens, procName);

        foreach (token; execution) {
            if (exitNow) {
                return;
            }
            try {
                push (token);

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
                            pop ();
                            execution.popFront ();
                            return;
                        }
                        evalSymbol (token);
                        continue;
                    default:
                }
            } 
            catch (Exception e) {
                if (0 < callDepth) {
                    -- callDepth;
                    throw e;
                }
                
                /// No exception handler left.
                stderr.writeln (stackTrace (token, e));
                this.exitNow = true;
                return;
            }
        }
    }

    string stackTrace (Cell token, Exception e = null) {
        string or (string val, string alt) {
            if (val != "")
                return val;
            else 
                return alt;
        }
        Cell sym (string val) {
            return Cell.fromSymbol (val);
        }
        Cell traces = execution.trace ();
        string [] msgs = [];
        
        if (e !is null) {
            msgs ~= 
                "\nStacky: Uncaught Exception\n  %s: %s: %s: %s"
                .format (typeid (e), e.file, e.line, e.msg);
        }

        if (traces != Cell.fromBool (false)) {
            foreach (Cell trace; traces.array) {
                Cell nope = sym ("??");
                
                // Get the values. The maybe empty.
                auto file = trace.lookup (sym ("file"), nope);
                auto func = trace.lookup (sym ("func"), nope);
                auto line = trace.lookup (sym ("line"), nope);
                auto tokn = trace.lookup (sym ("token"), nope);

                // Display the values, replace empty vals by ??.
                msgs ~= "  in %s: %s: %s\n    %s".format ( 
                        or (file.symbol, "??"), 
                        or (func.symbol, "??"), 
                        or (line.symbol, "??"), 
                        token); 
                        
            }
        }
        if (token !is null) {
            msgs ~= "  in %s: %s: %s\n    %s".format ( 
                        or (token.fileName,  "??"),
                        or (token.funcName,  "??"),
                        or (token.lineNo,    "??"),
                        token);
        }
        return msgs.join ("\n");
    }

    /// Evaluate a symbol.
    void evalSymbol (Cell op) {

        if (op.symbol.startsWith ("/")
        && !op.symbol.startsWith ("//")
        &&  op.symbol.length > 1)
        {
            return;
        }

        bool immediate = false; 
        Cell * match   = null;

        if (op.symbol.startsWith ("//")
        &&  op.symbol.length > 2)
        {
            immediate = true;
            match     = lookup (Cell.fromSymbol (op.symbol [2 .. $]));
        } else {
                
            match     = lookup (op);
        }

        if (! match) {
            throw new UnknownSymbol (op.toString);
        }

        if (immediate) {
            "eval symbol: %s immediate : %s".writefln (op.symbol, *match);
            execution.insert ([*match]);
            return;
        }

        pop ();
        
        if (match.kind == Cell.Proc) {
            evalProc (*match);
        } else {
            push (*match);
        }
    }

    void evalProc (bool nested = false) (Cell cell, Cell excHandler = null) {
        if (cell.kind != Cell.Proc) {
            throw new InvalidCellKind (
                    "Stacky.evalProc: cell is not a Proc.");
        }

        ExecutionStack backup = execution.dup;

        try {
            if (cell.proc.kind == Procedure.Native) {
                cell.proc.native (this);

            } else if (cell.proc.kind == Procedure.Words) {
                Cell [] code = cell.proc.code;
                
                if (nested) {
                    code ~=  Cell.fromSymbol ("exit");
                }
                ++ callDepth; 
                eval (cell.proc.code,
                      cell.proc.name);
                -- callDepth;
            }
        } catch (Exception e) {
            Cell token = operands.empty
                       ? null
                       : top;

            string traceStr = stackTrace (token, e);

            
            if (excHandler !is null) {
                // unwind the stack.
                execution.restoreFrom (backup);
                excManaged = false;
                
                // Push the exception on the stack.
                push (Cell.fromException (e));

                evalNested (excHandler);

                if (excManaged) {
                    return;
                }
            } 
            throw e; 
        }
    }

    alias evalNested = evalProc!true;
}

void stackyTest () {
    Stacky stacky = new Stacky; 

    //~assert (stacky.operands == []);
    //~
    //~stacky.push (Cell.from (1));
    //~stacky.push (Cell.from (2));

    //~assert (stacky.operands == [Cell.from (1), Cell.from (2)]);

    //~stacky.eval (`clear-stack`);
    //~assert (stacky.operands == []);
    //~
    //~stacky.eval ("1 2 3");
    //~assert (stacky.operands == map!(Cell.from) ([1L, 2L, 3L]).array);

    //~stacky.eval (`clear-stack 1 dup`);
    //~assert (stacky.operands == [Cell.from (1), Cell.from (1)]);

    //~stacky.eval (`clear-stack 1 2 3 drop swap`);
    //~assert (stacky.operands == [Cell.from (2), Cell.from (1)]);

    //~stacky.eval (`clear-stack 1 2 3 2 copy`);
    //~assert (stacky.operands 
    //~        == map!(Cell.from) ([1, 2, 3, 2, 3]).array);

    //~stacky.eval (`clear-stack 1 2 3 2 rolln`);
    //~assert (stacky.operands 
    //~        == map!(Cell.from) ([3, 2, 1]).array,
    //~        "operands: %s".format (stacky.operands));

    //~stacky.eval (`clear-stack mark "hello" "world" count-to-mark`);
    //~assert (stacky.top == Cell.from (2));
    //~
    //~stacky.eval (`clear-to-mark`);
    //~assert (stacky.operands == []);

    //~stacky.eval (`clear-stack ( 1 2 3 )`);
    //~assert (stacky.top == Cell.from ([1L, 2L, 3L]));

    //~stacky.eval (`clear-stack [ "hello" "world" ]`);
    //~assert (stacky.top == Cell.from (["hello": "world"]));

    //~stacky.eval (`clear-stack { dup dup }`);
    //~assert (stacky.top.kind == Cell.Proc);
    //~assert (stacky.top.proc.code 
    //~        == map!(Cell.fromSymbol) (["dup", "dup"]).array);

    //~assert (stacky.dicts.top.dict.keys.empty);
    //~stacky.eval (`clear-stack /2dup { dup dup } def print-stack`);
    //~assert (! stacky.dicts.top.dict.keys.empty);

    //~stacky.eval (`clear-stack 1 2 2dup`);
    //~assert (stacky.operands
    //~        == map!(Cell.from) ([1, 2, 2, 2]).array);

    //~stacky.eval (`clear-stack 1 2 stack-length`);
    //~assert (stacky.operands.top == Cell.from (2));

    //~stacky.eval (`clear-stack 1 2 + 3 =`);
    //~assert (stacky.operands.top == Cell.fromBool (true));

    //~stacky.eval (`clear-stack 3.0 4 * 12.0 = `);
    //~assert (stacky.operands.top == Cell.fromBool (true));

    //~stacky.eval (`clear-stack ( 1 2 3 ) { 2 + } for-all`);
    //~assert (stacky.operands
    //~        == map!(Cell.from) ([3, 4, 5]).array);

    //~stacky.eval (`clear-stack true { "toto" } if`);
    //~assert (stacky.operands.top == Cell.from ("toto"));

    //~stacky.eval (`clear-stack false { "yep" } { "nope" } ifelse`);
    //~assert (stacky.operands.top == Cell.from ("nope"));

    //~stacky.eval (`clear-stack ( 0 1 2 3 ) 1 get`);
    //~assert (stacky.operands.top == Cell.from (1));

    //~stacky.eval (`clear-stack "hello" 1 get`);
    //~assert (stacky.operands.top == Cell.from ("e"));

    //~stacky.eval (`
    //~    clear-stack

    //~    /all { 
    //~        [] begin 
    //~        /proc   swap def 
    //~        /array  swap def
    //~        /status true def
    //~        
    //~        array { 
    //~            proc true = not { 
    //~                /status false def 
    //~            } if 
    //~        } for-all
    //~        
    //~        status
    //~        end
    //~    } def 
    //~`);
    //~stacky.eval (` ( 1 2 3 ) { 5 < } all `);
    //~assert (stacky.operands.top == Cell.fromBool (true));
    //~
    //~stacky.eval (`
    //~    clear-stack

    //~    /any { 
    //~        [] begin 
    //~        /proc   swap def 
    //~        /array  swap def
    //~        
    //~        array { 
    //~            proc true = { 
    //~                true 
    //~                return
    //~            } if 
    //~        } for-all
    //~        
    //~        end
    //~    } def 

    //~    ( 1 2 3 ) { 5 < } any
    //~`);
    //~assert (stacky.operands.top == Cell.fromBool (true));

    //~stacky.eval (`
    //~    clear-stack

    //~    /map {
    //~        [] begin
    //~        /proc   swap  def
    //~        /source swap  def
    //~        /target  ()   def 

    //~        source { proc target push } for-all

    //~        target
    //~        end
    //~    } def
    //~`);
    //~stacky.eval (` 
    //~    ( 1 2 3 ) { 2 * } map 
    //~    ( 2 4 6 ) = 
    //~`);
    //~assert (stacky.operands.top == Cell.fromBool (true));

    //~stacky.eval (`
    //~    clear-stack

    //~    /filter {
    //~        [] begin
    //~        /proc   swap def
    //~        /source swap def 
    //~        /target  ()  def

    //~        source {
    //~            dup proc true =
    //~            { target push } { drop } if-else
    //~        } for-all
    //~        
    //~        target
    //~        end
    //~    } def

    //~    ( 1 9 3 10 4 16 ) { 5 > } filter
    //~    ( 9 10 16 ) =
    //~`);
    //~assert (stacky.operands.top == Cell.fromBool (true));
    //~
    //~stacky.eval (`
    //~    clear-stack

    //~    10 (
    //~        { 5 > } {  "> 5" }
    //~        /else   { "<= 5" }
    //~    ) cond

    //~    "> 5" =
    //~`);
    //~assert (stacky.operands.top == Cell.fromBool (true));
    //~
    //~stacky.eval (`
    //~    clear-stack
    //~    "hello" [ "hello" "world" ] known 
    //~`);
    //~assert (stacky.operands.top == Cell.fromBool (true));
    //~
    //~stacky.eval (`
    //~    clear-stack
    //~    [ /hello "world" ] begin
    //~        /hello "tomato" store
    //~        hello "tomato" =
    //~    end
    //~`);
    //~assert (stacky.operands.top == Cell.fromBool (true));
    //~
    //~stacky.eval (`
    //~    clear-stack

    //~    [] begin
    //~        /dict [ /hello "world" ] def
    //~        dict /hello undef
    //~        dict [] = 
    //~    end
    //~`);
    //~assert (stacky.operands.top == Cell.fromBool (true));
    //~
    //~stacky.eval (`
    //~    clear-stack

    //~    [] begin
    //~        /dict 1 def
    //~        /dict where
    //~    end
    //~`);
    //~assert (stacky.operands.top == Cell.fromBool (true));
    
    stacky.eval (`
        clear-stack

        /test-exception {
            [] begin
            /sub-function {
                % 1 0 /
                1 +
            } def 

            sub-function
            end
        } def

        { test-exception } (
            /StackUnderflow { drop "stack underflow detected" print-stack }
            /Exception { drop "recovering from exception" print-stack }
        ) try-catch
    `);

    "%s".writefln ('*'.repeat (30));
    stacky.operands.writeln;
    stacky.execution.dup.writeln;
}

void repl () {
    auto stacky = new Stacky;
    
    `stacky> `.write;
    foreach (line; stdin.byLine) {
        string code = `#file "<stdin>" #function "main"` ~ "\n" 
                    ~ line.to!string;
        stacky.eval (code, "main");
        stacky.eval ("print-stack");
        `stacky> `.write;
    }
}

void main () {
    grammarTest ();
    cellTest ();
    parseTest ();
    stackyTest ();

    //repl ();
}
