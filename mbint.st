#!/afs/cats.ucsc.edu/courses/cse112-wm/usr/smalltalk/bin/gst -f
"$Id: mbint.st,v 1.16 2021-02-11 19:21:43-08 - - $"
"Jay Pandit(jpandit@ucsc.edu)"
"Tanisha Khemka(tkhemka@ucsc.edu)"

"given"
Object subclass: NumberStream [
   |atEndFlag stream buffer|
   NumberStream class >> new [
      ^ super new init: stdin.
   ]
   NumberStream class >> new: aStream [
      ^ super new init: aStream.
   ]
   init: aStream [
      atEndFlag := false.
      stream := aStream.
      buffer := OrderedCollection new.
   ]
   atEnd [ ^ atEndFlag ]
   nextNumber [
      [atEndFlag] whileFalse: [
         buffer size > 0 ifTrue: [
            ^ buffer removeFirst asNumber asFloatD.
         ].
         stdout flush.
         stderr flush.
         stream atEnd
            ifTrue: [atEndFlag := true]
            ifFalse: [buffer := stream nextLine substrings: ' ']
      ].
      ^ 0.0 / 0.0 "NaN".
   ]
].


"given"
Object subclass: Debug [
   level := 0.  "multiple -d, -dd, -ddd options set debug level"
   Debug class >> incr [level := level + 1]
   Debug class >> > isNumber [^ level > isNumber]
].


"given"
Object subclass: MiniBasic [
   nl := Character nl.
   MiniBasic class >> unimplemented: object [
      |caller|
      caller := thisContext parentContext.
      stdout << object class << ' inherits '
             << caller method << ': ' << object << nl.
   ] 
   prefix [^ '(', self class printString, ' ']
   assertionFailed: message [
      stderr << 'Assertion Failed: ' << message << nl.
      stderr << self << nl.
      ObjectMemory quit: 1.
   ]
].

"given"
MiniBasic subclass: Expr [
   nan := 0.0 / 0.0.
   printOn: file [^ file << self prefix << ')']
   isNumber [MiniBasic unimplemented: self. ^ nan]
].


"given"
Expr subclass: NumExpr [
   |isNumber|
   NumExpr class >> new: val [^ super new init: val]
   init: val [isNumber := val + 0.0d0]
   printOn: file [^ file << self prefix << isNumber << ')']
   isNumber [^ isNumber]
].


"given"
Expr subclass: VarExpr [
   |variable|
   varDict := Dictionary from: {
      #e   -> 1.0 exp.
      #eof -> 0.0.
      #nan -> (0.0 / 0.0).
      #pi  -> -1.0 arcCos.
   }.
   VarExpr class >> new: var [^ super new init: var]
   init: var [variable := var]
   printOn: file [^ file << self prefix << variable << ')']
   put: val [varDict at: variable put: val]
   isNumber [^ varDict at: variable ifAbsent: [0.0]]
   get_data [^ variable]
].


"Given + added"
Expr subclass: UnopExpr [
   |oper opnd|
   UnopExpr class >> new: op with: opn [
      ^ super new init: op init: opn.
   ]
   init: op init: opn [
      oper := op. opnd := opn.
   ]
   printOn: file [
      ^ file << self prefix << oper << ' ' << opnd << ')'.
   ]
   isNumber [  "use perform"
      ^((opnd isNumber) perform: oper)  "oper is a symbol"
   ]
].


"Given + added"
Expr subclass: BinopExpr [
   |oper opnd1 opnd2|
   BinopExpr class >> new: op with: opn1 with: opn2 [
      ^ super new init: op with: opn1 with: opn2.
   ]
   init: op with: opn1 with: opn2 [  "new calls init which stores the values of instance varaiables"
      oper := op. opnd1 := opn1. opnd2 := opn2.
   ]
   printOn: file [
      ^ file << self prefix << oper << ' ' << opnd1
             << ' ' << opnd2 << ')'.
   ]
   array_expression [^ opnd1]  "use perform with"
   array_index [^ opnd2]
   isNumber [
      oper = #aget
      ifFalse:[
         ^ opnd1 isNumber perform: oper with: opnd2 isNumber
      ]
      ifTrue: [
         ^ ArrayExpr aget: opnd1 get_data 
               with:opnd2 isNumber rounded + 1.
      ]
   ]
].


"Given + added"
Expr subclass: ArrayExpr [   "Storing array name in array dict"
   |arrayName|
   arrayDict := Dictionary new.
   ArrayExpr class >> new: var [^ super new init: var]
   init: var [arrayName := var]
   printOn: file [^ file << self prefix << arrayName << ')']
   ArrayExpr class >> aget: name with: index [             "look up the array anme in the array dict"
            ^ (arrayDict at: name) at: (index rounded)]
   ArrayExpr class >> put: name with: index with: 
            val [(arrayDict at: name) at: index put: val]
   ArrayExpr class >> add_array: name with: 
            new_array [arrayDict at: name put: new_array]   "add to array dict"
].


"Given - added"
Expr extend [
   Expr class >> parse: expr [
      expr isNumber ifTrue: [^ NumExpr new: expr].
      expr isSymbol ifTrue: [^ VarExpr new: expr].
      expr isArray ifTrue: [
         expr size = 2 ifTrue: [
            ^ UnopExpr new: (expr at: 1)
                       with: (Expr parse: (expr at: 2)).
         ].
         expr size = 3 ifTrue: [
            ^ BinopExpr new: (expr at: 1)
                        with: (ArrayExpr parse: (expr at: 2))
                        with: (Expr parse: (expr at: 3)).
         ]
         ifFalse: [
               ^ BinopExpr new: (expr at: 1)
                           with: (Expr parse: (expr at: 2))
                           with: (Expr parse: (expr at: 3)).
         ]
         .
         self assertionFailed: 'Expr>>parse: isArray wrong size'.
      ].
      self assertionFailed: 'Expr>>parse: expr wrong type'.
   ]
].


"Given + added"
MiniBasic subclass: Stmt [  "contains label stmt"
   stmtNr := 1.
   Stmt class >> getStmtNr [^  stmtNr]
   Stmt class >> incrStmtNr [ stmtNr := 1 +  stmtNr]  "class method to increment the Stmt Number"
   labelDict := Dictionary new.
   printOn: file [^ file << self prefix << ')']  "debugger"
   interp [MiniBasic unimplemented: self.]
   Stmt class >> update: label with: index [
      labelDict at: label put: index
   ]
].


"given + define interp"
Stmt subclass: DimStmt [
   |name size|
   DimStmt class >> new: stmt [^ super new init: stmt]
   init: stmt [
      name := Expr parse: (stmt at: 2).
      size := Expr parse: (stmt at: 3).
   ]
   printOn: file [^ file << self prefix << name << ' ' << size << ')']
   interp[
      |array2|
      array2 := Array new: (size isNumber rounded) withAll: 0.0d0.   "create a new array"
      ArrayExpr add_array: (name get_data) with: array2.   "inserts the element into the new array"
   ]
].


"given + define interp"
"interp: looks up the name or finds the array, sends the value message through expr and stores the data"
Stmt subclass: LetStmt [
   |name expr|
   LetStmt class >> new: stmt [^ super new init: stmt]
   init: stmt [
      name := Expr parse: (stmt at: 2).
      expr := Expr parse: (stmt at: 3).
   ]
   printOn: file [^ file << self prefix << name << ' ' << expr << ')']
   interp [
      name class = BinopExpr
      ifFalse: [ 
         name put: expr isNumber
      ]
      ifTrue: [
         ArrayExpr put: (name array_expression) get_data 
               with: 1 + ((name array_index) isNumber rounded) "since array start at 1 and not 0"
                  with: (expr isNumber).
      ]
   ]
].


"given + define interp"
Stmt subclass: GotoStmt [
   |label|
   GotoStmt class >> new: stmt [^ super new init: stmt]
   init: stmt [label := stmt at: 2]
   printOn: file [^ file << self prefix << label << ')']
   interp [
       stmtNr := labelDict at: label.   "calls the set statement and then ask the statement to look up in dictionary"
   ] 
].


"given + define interp"
Stmt subclass: IfStmt [
   |expr label|
   IfStmt class >> new: stmt [^ super new init: stmt]
   init: stmt [
      expr := Expr parse: (stmt at: 2).
      label := stmt at: 3.
   ]
   printOn: file [^ file << self prefix << expr << ' ' << label << ')']
   interp [   "send isNumber message to expr and if true, go to goto function, else do nothing"
      expr isNumber ifTrue: [
          stmtNr := labelDict at: label.
      ]
   ] 
].

"given + added"
"looks at input variable, calls standard input num, nextnum, then prints"
"if returns eof, set eof to num 1."
Stmt subclass: InputStmt [
   |inputVars|
   stdinNumbers := NumberStream new.
   InputStmt class >> new: stmt [^ super new init: stmt]
   init: stmt [
      |args|
      args := stmt at: 2.
      inputVars := Array new: args size.
      1 to: args size do: [:index|
         inputVars at: index put: (Expr parse: (args at: index)).
      ]
   ]
   printOn: file [^ file << self prefix << inputVars << ')']
   interp [
      inputVars do: [: var |
         |isNumber|
         isNumber := stdinNumbers nextNumber.
         stdinNumbers atEnd
         ifFalse: [
            var put: isNumber.
         ]
         ifTrue: [
            (VarExpr new: #eof) put: 1.0
         ]
      ].
   ]
].


"given"
Stmt subclass: PrintStmt [
   |printables|
   PrintStmt class >> new: stmt [^ super new init: stmt]
   init: stmt [
      |args|
      args := stmt at: 2.
      printables := Array new: args size.
      1 to: args size do: [:index|
         |arg|
         arg := args at: index.
         arg isString ifFalse: [ arg := Expr parse: arg].
         printables at: index put: arg.
      ]
   ]
   printOn: file [^ file << self prefix << printables << ')']
   interp [
      Debug > 2 ifTrue: [printables inspect].
      printables do: [:obj|
         obj isString ifTrue: [stdout << obj]
                      ifFalse: [stdout << ' ' << obj isNumber].
      ].
      stdout << nl.
   ]
].


"given"
Stmt subclass: NullStmt [
   NullStmt class >> new: stmt [^ super new]
   printOn: file [^ file << self prefix << ')']
   interp []
].


"given"
Stmt extend [
   stmtDict := Dictionary from: {
      #dim   -> DimStmt.
      #let   -> LetStmt.
      #goto  -> GotoStmt.
      #if    -> IfStmt.
      #input -> InputStmt.
      #print -> PrintStmt.
      #null  -> NullStmt.
   }.
   Stmt class >> parse: stmt [
      |stmtSym stmtClass|
      stmt size = 0 ifTrue: [stmtSym := #null]
                    ifFalse: [stmtSym := stmt at: 1].
      stmtClass := stmtDict at: stmtSym.
      ^ stmtClass new: stmt.
   ]
]


"given + added"
MiniBasic subclass: Interpreter [
   |statements|
   Interpreter class >> new: program [^ super new init: program]
   init: program [
      statements := Array new: program size.
      1 to: program size do: [:index|
         |stmt parsed|
         stmt := (program at: index) at: 3.
         statements at: index put: (Stmt parse: stmt).
      ].
   ]

   print [
      stdout << 'Interpreter statements: [' << nl.
      1 to: statements size do: [:index|
         stdout << '   ' << index << ': '
                << (statements at: index) << nl.
      ].
      stdout << '].' << nl.
   ]

   interpret [
      | stmtNr|
      [ stmtNr := Stmt getStmtNr.  stmtNr <= statements size]
      whileTrue: [
         |stmtObj|
         Stmt incrStmtNr.
         stmtObj := statements at:  stmtNr.
         Debug > 1 ifTrue: [
            stdout <<  stmtNr << ': ' << stmtObj << nl
         ].
         stmtObj interp.
      ]
   ]
].

"given"
Object subclass: Main [
   nl := Character nl.
   scriptName := thisContext currentFileName.

   Main class >> usage [
      stderr << 'Usage: ' << scriptName << ' [-d] fileName' << nl.
      ObjectMemory quit: 1.
   ]

   Main class >> print: program [
      stdout << 'Main program: [' << nl.
      1 to: program size do: [:index|
         stdout << '   ' << index << ': ' << (program at: index) << nl.
      ].
      stdout << '].' << nl.
   ]


"given"
   Main class >> getopts [
      |fileName|
      Smalltalk arguments: '-d' do: [:opt :arg|
         opt = $d ifTrue: [Debug incr].
         opt = nil ifTrue: [
            fileName isNil ifFalse: [Main usage isNumber].
            fileName := arg.
         ].
      ] ifError: [Main usage isNumber].
      Debug > 0 ifTrue: [
         stdout << scriptName << ': ' << Smalltalk arguments << nl.
      ].
      ^ fileName.
   ]


    "line 437 - 445 and 454- 463 are given and we are filling in the dictionary label table "  
Main class >> main [
    |fileName|
    fileName := Main getopts.
    fileName isNil ifTrue: [Main usage isNumber].
    [
        |program interpreter|
        FileStream fileIn: fileName.
        program := Program get.
        Debug > 0 ifTrue: [Main print: program].
        "Pre-processing: fill in the labelDict"

        1 to: program size do: [:count| 
            |label index|
            index := count.
            label := ((program at: count) at:2).
            Stmt update: label with: index.].

        interpreter := Interpreter new: program.
        Debug > 0 ifTrue: [interpreter print].
        interpreter interpret.
    ] on: SystemExceptions.FileError do: [:signal|
        stderr << scriptName << ': ' << fileName << ': '
            << signal messageText << nl.
        ObjectMemory quit: 1.
    ].
]
].

Main main.
