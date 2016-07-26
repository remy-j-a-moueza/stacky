import std.stdio;
import std.range;
import std.conv;
import std.string;
import std.algorithm;
import std.array;
import std.digest.sha;

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
struct Procedure {
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

    /// Create a procedure from an array of code.
    static Procedure fromCode (Cell [] code) {
        Procedure self =  { 
            kind: Words,
            code: code
        };
        return self;
    }

    /// Create a procedure from a D delegate.
    static Procedure fromDelegate (NativeType native) {
        Procedure self =  { 
            kind  : Native,
            native: native
        };
        return self;
    }

    /// Return a string representation.
    string toString () {
        switch (kind) {
            case Words:
                return "<proc: code %s>".format (code.to!string);
            case Native:
                return "<proc: native %x>".format (&native);
            default:
                return "<proc: empty>";
        }
    }
    
    /** Test for equality betweeen procedures.
      Compare pointers for native procedures.
      Compare arrays of code for words procedures.
     */
    bool opEquals (ref const Procedure proc) const pure {
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
    int opCmp (ref const Procedure proc) const pure {
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
            Cell cCode = { 
                kind: Cell.Array,
                array: code.dup
            };
            Cell cProc = {
                kind: Cell.Array,
                array: proc.code.dup
            };

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
struct Cell {
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

    /// Initialization from a long value.
    static Cell fromLong (long val) {
        Cell self = { 
            kind    : Cell.Integer,
            integer : val
        };
        return self;
    }

    /// Initialization from a double value.
    static Cell fromDouble (double val) {
        Cell self = { 
            kind     : Cell.Floating,
            floating : val
        };
        return self;
    }
    
    /// Initialization from a string value.
    static Cell fromString (string val) {
        Cell self = { 
            kind: Cell.String,
            text: val
        };
        return self;
    }

    /// Initialization as a symbol from a string value.
    static Cell symbolNew (string val) {
        Cell self = {
            kind   : Cell.Symbol, 
            symbol : val
        };
        return self;
    }
    
    /// Initialization from a boolean value.
    static Cell fromBool (bool val) {
        Cell self = {
            kind    : Cell.Bool,
            boolean : val
        };
        return self;
    }
    
    /// Initialization as an empty array.
    static Cell arrayNew () {
        Cell self = {
            kind: Cell.Array, 
            array: []
        };
        return self;
    }
    
    /// Initialization as a procedure from an array of words.
    static Cell procFromCode (Cell [] array) {
        Cell self = {
            kind: Cell.Proc, 
            proc: Procedure.fromCode (array)
        };
        return self;
    }

    /// Initialization as a procedure from a D delegate.
    static Cell procFromNative (Procedure.NativeType native) {
        Cell self = { 
            kind: Cell.Proc,
            proc: Procedure.fromDelegate (native)
        };
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
        Cell self = { 
            kind: Dict,
            dict: null
        };

        foreach (k, v; dict) {
            Cell key = Cell.from!(stringKind) (k); 
            Cell val = Cell.from!(stringKind) (v);

            self.dict [key.sha1Hash] = [key, val];
        }

        return self;
    }
    
    
    
    static Cell dictNew () {
        Cell self = { 
            kind: Cell.Dict,
            dict: null
        };
        return self;
    }
    
    string toString () {
        switch (kind) {
            case Integer:
                return integer.to!string ~ "d";
            case Floating:
                return floating.to!string ~ "f";
            case String:
                return "\"" ~ text ~ "\"";
            case Symbol:
                return symbol;
            case Bool:
                return boolean.to!string;
            case Array:
                return array.to!string;
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
    bool opEquals (ref const Cell cell) const pure {
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
    int opCmp (ref const Cell cell) const pure {
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

    assert (anInt.toString   == "0d");
    assert (aReal.toString   == "0f");
    assert (aString.toString == `"hello"`);
    assert (aBool.toString   == "true");
    assert (anArray.toString == `["hello", "world"]`);

    anInt.writeln; 
    aReal.writeln;
    aString.writeln;
    aBool.writeln;
    anArray.writeln;
    dict.writeln;
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
    assert (tokens == map!(Cell.from) ([1L, 2L, 3L]).array);

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

class Stacky {
    
    /// Operand stack. The top is the end of the array.
    Cell [] operands;
    
    /// Execution stack: tokens to be interpreted.
    Cell [][] execution;
    
    /// Dictionary stack.
    Cell [] dicts;

    /// Instruction pointer.
    size_t ip = 0;
    
    /// Execution (tokens) pointer.
    size_t ep = 0;

    Cell top () {
        return operands [0.. ip].top; 
    }

    Cell index (size_t n) {
        Cell [] slice = operands [0 .. ip];
        
        if (slice.length < n) {
            throw new StackUnderflow ("index: stack too short.");
        }

        return slice [ip - n]; 
    }

    void push (Cell cell) {
        operands ~= cell;
        ip ++;
        "push (%s), ip == %d".writefln (cell, ip);
    }

    this () {
        dicts ~= builtinWords ();
    }


    Cell builtinWords () {
        Procedure.NativeType [string] procs;
        
        /// Discard all elements on the stack.
        procs ["clear"] = (Stacky stacky) {
            stacky.operands = stacky.operands [0 .. stacky.ip];
        };
        
        /// Removes one element at the top of the stack.
        procs ["pop"] = (Stacky stacky) {
            "pop: before: ip (%d), %s".writefln (stacky.ip, stacky.operands);
            
            if (stacky.operands.length < 1) {
                throw new StackUnderflow ("pop");
            }
            stacky.operands.length -= 1; 
            //if (stacky.operands.length == stacky.ip) {
            //    stacky.operands.length -= 1;

            //} else { 
            //    stacky.operands 
            //        =  stacky.operands [0     .. stacky.ip]
            //        ~  stacky.operands [stacky.ip +1 .. $];
            //}
            "pop: after %s".writefln (stacky.operands);
            -- stacky.ip;
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
            procs ["pop"] (stacky);
            Cell bottom = stacky.top;
            procs ["pop"] (stacky);

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
            procs ["pop"] (stacky);
            
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
            procs ["pop"] (stacky);
            
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

        procs ["print-stack"] = (Stacky stacky) {
            //"print-stack: to ip : %s".writefln (stacky.operands [0 ..ip]);
            "print-stack: all   : %s".writefln (stacky.operands);
            string [] vals; 

            foreach (cell; stacky.operands [0 .. ip]) {
                vals ~= cell.toString; 
            }

            vals.join (" ").writeln;
        };

        procs ["("] = (Stacky stacky) {
            stacky.push (Cell.from!"symbol" ("("));
        };

        procs [")"] = (Stacky stacky) {
            Cell tokens = {
                kind: Cell.Array,
                array: []
            };
            
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
                procs ["pop"] (stacky);
            }
            // Remove the openning '('.
            procs ["pop"] (stacky);

            stacky.push (tokens);
        };
        
        procs ["["] = (Stacky stacky) {
            stacky.push (Cell.from!"symbol" ("["));
        };

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
                procs ["pop"] (stacky);
            }
            // Remove the openning '['.
            procs ["pop"] (stacky);
            
            Cell dict = {
                kind: Cell.Dict,
                dict: null
            };
            
            for (size_t i = 0; i < tokens.length; ++ i) {
                Cell key = tokens [i ++]; 
                Cell val = tokens [i];
                
                dict.dict [key.sha1Hash] = [key, val];
            }
            stacky.push (dict);
        };
        
        procs ["{"] = (Stacky stacky) {
            stacky.push (Cell.from!"symbol" ("{"));
        };
        
        procs ["}"] = (Stacky stacky) {
            size_t index = 0; 
            bool found   = false;

            foreach_reverse (cell; stacky.operands [0 .. stacky.ip]) {
                if (cell.kind == Cell.Symbol
                &&  cell.symbol == "{") {
                    found = true;
                    break;
                }
                index ++;
            }
            if (! found) {
                throw new Exception ("Unbalanced proc '{}' parenthesis");
            }

            Cell [] tokens = stacky.operands [stacky.ip - index .. stacky.ip];

            foreach (num; stacky.ip - index .. stacky.ip) {
                procs ["pop"] (stacky);
            }
            // Remove the openning '{'.
            procs ["pop"] (stacky);

            stacky.push (Cell.procFromCode (tokens));
        };


        return Cell.from!("symbol", string, Procedure.NativeType) (procs);
    }

    Cell * lookup (Cell symbol) {
        Cell * match;

        foreach (dict; dicts) {
            match = dict.lookup (symbol);
            
            if (match) {
                return match;
            }
        }
        return match;
    }

    Cell * lookup (string symbol) {
        return lookup (Cell.from!"symbol" (symbol));
    }

    bool hasNextToken () {
        "hasNextToken: ep %d, exe-length: %d, top-length %d"
            .writefln (
                    ep, 
                    execution.length, 
                    execution [$ -1].length);

        if (execution.length < 1) {
            return false;
        }

        if (execution [$ -1].length <= ep
        &&  execution.length  <= 1) {
            return false;
        }
        return true;
    }

    Cell nextToken () {
        if (! hasNextToken ()) {
            throw new StackUnderflow ("No longer any tokens.");
        }

        if (ep > execution [$ -1].length) {
            ep = 0;
            execution.length -= 1;

            if (! hasNextToken ()) {
                throw new StackUnderflow (
                    "No longer any tokens after execution stack pop.");
            }
        }

        "ep: %s, execution [$ -1]: %s".writefln (ep, execution [$ -1]);
        return execution [$ -1][ep ++];
    }

    void eval (string input) {
        "eval: operands: %s".writefln (operands);
        execution ~= parse (input);
        ep = 0;

        while (hasNextToken ()) {
            Cell token = nextToken ();
            push (token);
            "eval ++ ip: %d".writefln (ip);

            switch (token.kind) {
                case Cell.Integer: 
                case Cell.Floating:
                case Cell.String: 
                case Cell.Bool:
                case Cell.Array:
                case Cell.Dict:
                case Cell.Proc:
                    "eval ++ ip: %d".writefln (ip);
                    continue;

                case Cell.Symbol:
                    evalSymbol (token);
                    continue;
                default:
            }
        }
        execution.length -= 1;
    }

    void evalSymbol (ref Cell op) {
        "eval symbol %s".writefln (op);
        if (op.symbol.startsWith ("/")
        &&  op.symbol.length > 1)
        {
            op.symbol = op.symbol [1..$];
            return;
        }

        Cell * match = lookup (op);

        if (! match) {
            throw new Exception (
                "Unknown symbol: "
                ~ op.toString);
        }

        "eval symbol: match : %s".writefln (*match);
        "eval symbol pop: before, stack: %s".writefln (operands);
        lookup ("pop").proc.native (this);
        
        "eval symbol pop: after, stack: %s".writefln (operands);

        
        if (match.proc.kind == Procedure.Native) {
            "eval native!".writeln;
            match.proc.native (this);

        } else if (match.proc.kind == Procedure.Words) {
            size_t saveIp = ip;

            foreach (cell; match.proc.code.array) {
                push (cell);
            }
            ip = saveIp;
        }
    }
}

void stackyTest () {
    Stacky stacky = new Stacky; 

    assert (stacky.operands == []);
    
    //stacky.push (Cell.from (1));
    //stacky.push (Cell.from (2));

    stacky.operands.writeln;
    stacky.eval ("1 2 3 print-stack");
    stacky.eval ("dup print-stack");
    stacky.eval ("drop swap print-stack");
    stacky.eval ("2 copy print-stack");
    stacky.eval ("3 rolln print-stack");
    stacky.eval (`mark "hello" "world" count-to-mark print-stack`);
    stacky.eval (`clear-to-mark print-stack`);
    stacky.eval (`( 1 2 3 ) print-stack`);
    stacky.eval (`[ "hello" "world" ] print-stack`);
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
