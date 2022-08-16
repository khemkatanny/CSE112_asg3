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
   level := 0.
   Debug class >> incr [level := level + 1]
   Debug class >> > value [^ level > value]
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
   value [MiniBasic unimplemented: self. ^ nan]
].

"Given"
Expr subclass: NumExpr [
   |value|
   NumExpr class >> new: val [^ super new init: val]
   init: val [value := val + 0.0d0]
   printOn: file [^ file << self prefix << value << ')']
   value [^ value]
].

"Given"
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
   value [^ varDict at: variable ifAbsent: [0.0]]
   get_data [^ variable]
].

"added value method"
"Done!!!"
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
   value [^ (opnd value perform: oper) asFloatD]
].

"Change variables and comment"
"added value method"
Expr subclass: BinopExpr [
   |oper opnd1 opnd2|  "declaring variables"
   BinopExpr class >> new: op with: opn1 with: opn2 [
      ^ super new init: op with: opn1 with: opn2.
   ]
   init: op with: opn1 with: opn2 [
      oper := op. opnd1 := opn1. opnd2 := opn2.
   ]
   printOn: file [
      ^ file << self prefix << oper << ' ' << opnd1
             << ' ' << opnd2 << ')'.
   ]
   value[
      oper = #aget
      ifTrue: [
         ^ opnd1 oper: (((opnd2 value) asInteger) + 1).
      ]
      ifFalse: [
         ^ opnd1 value perform: oper with: opnd2 value.
      ]
   ]
  getOper [^ oper]
  getOpnd1 [^ opnd1]
  getOpnd2 [^ opnd2]
].

"Change variables and comment"
Expr subclass: ArrayExpr [
   |arrayName|
   arrayDict := Dictionary new.
   ArrayExpr class >> new: var [^ super new init: var]
   init: var [arrayName := var]
   printOn: file [^ file << self prefix << arrayName << ')']
   aget: index [^ (arrayDict at: arrayName) at: index]
   aput: index with: value [ (arrayDict at: arrayName) 
                              at: index put: value]
   addArray: arr [arrayDict at: arrayName put: arr] 
].


"given"
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
            ((expr at: 1) = #aget) | ((expr at: 1) = #aput)
            ifTrue: [
               ^ BinopExpr new: (expr at: 1)
                           with: (ArrayExpr new: (expr at: 2))
                           with: (Expr parse: (expr at: 3)).
            ]
            ifFalse: [
               ^ BinopExpr new: (expr at: 1)
                           with: (Expr parse: (expr at: 2))
                           with: (Expr parse: (expr at: 3)).
            ]
         ].
         self assertionFailed: 'Expr>>parse: isArray wrong size'.
      ].
      self assertionFailed: 'Expr>>parse: expr wrong type'.
   ]
].

"comment"
"added class methods after labelDict: addStmtLabel and findStmtLabel"  
"DONE!!!!"
"class method to get the Stmt Number"
MiniBasic subclass: Stmt [ "abstract base class"
   stmtNr := 1.    "used to get Stmt numbers"
   Stmt class >> getStmtNr [^ stmtNr]  
   Stmt class >> incrStmtNr [stmtNr := stmtNr + 1]  "class method to increment the Stmt Number"
   labelDict := Dictionary new.  "have to write a loop to scan over the entire program and load labelDict - addlabel, findlabel"
   Stmt class >> addStmtLabel: label to: index [labelDict at: label put: index]
   Stmt class >> findStmtLabel: label [stmtNr := labelDict at: label]
   printOn: file [^ file << self prefix << ')']  "print is used for debugging"
   "interp [MiniBasic unimplemented: self.]"
].

"added a method: interp"
"change the method little bit"
Stmt subclass: DimStmt [
   |name size|
   DimStmt class >> new: stmt [^ super new init: stmt]
   init: stmt [
      name := ArrayExpr new: (stmt at: 2).
      size := Expr parse: (stmt at: 3).
   ]
   printOn: file [^ file << self prefix << name << ' ' << size << ')']
   interp[
      |new_array|
      new_array := Array new: (size value rounded) withAll: 0.0d0.
      name addArray: new_array.
   ]
].

"add interp method: looks up the name or finds the array, sends the value message through expr and stores the data"
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
         name put: expr value
      ]
      ifTrue: [
         |array_expression index num|
         index := name array_index.
         array_expression := name array_expression.
         ArrayExpr put: array_expression get_data with: 
                  1 + (index value rounded) with: (expr value).
      ]
   ]
].

"added method interp: calls setStmt, ask stmt to look up something in Dict"
Stmt subclass: GotoStmt [
   |label|
   GotoStmt class >> new: stmt [^ super new init: stmt]
   init: stmt [label := stmt at: 2]
   interp [
      Stmt findStmtLabel: label.
   ]
   printOn: file [^ file << self prefix << label << ')']
].


"added method interp: send the value method/message? to expr, if true, do what goto does, if false, dont do anything"
Stmt subclass: IfStmt [
   |expr label|
   IfStmt class >> new: stmt [^ super new init: stmt]
   init: stmt [
      expr := Expr parse: (stmt at: 2).
      label := stmt at: 3.
   ]
   printOn: file [^ file << self prefix << expr << ' ' << label << ')']
   interp [
      expr value ifTrue: [ Stmt findStmtLabel: label.]
   ]
].


"looks at inpur variable, calls standard input num, nextnum, then prints"
"modify: if returns eof, set eof to num 1."
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
      inputVars do: [:var|
         |value eof_new|
         value := stdinNumbers nextNumber.
         stdinNumbers atEnd ifTrue: [
            eof_new := VarExpr new: #eof.  "if eof is 0, check for eof,if eof set to 1. If eof not 0 then we return nan"
            eof_new put: 1.0.
         ]
         ifFalse: [
            var put: value.
         ]
      ].
   ]
].


" Given "
Stmt subclass: PrintStmt [
   |printables|
   PrintStmt class >> new: stmt [^ super new init: stmt]
   init: stmt [
      |args|
      args := stmt at: 2.  "stmt at 2 is an array"
      printables := Array new: args size.  "allocate an array with new args size to class Array"
      1 to: args size do: [:index|  
         |arg|
         arg := args at: index.
         arg isString ifFalse: [ arg := Expr parse: arg].  "if not a stirng then should be an expr"
         printables at: index put: arg.
      ]
   ]
   printOn: file [^ file << self prefix << printables << ')']
   interp [
      Debug > 2 ifTrue: [printables inspect].
      printables do: [:obj|
         obj isString ifTrue: [stdout << obj]
                      ifFalse: [stdout << ' ' << obj value].
      ].
      stdout << nl.
   ]
].


" Given "
Stmt subclass: NullStmt [
   NullStmt class >> new: stmt [^ super new]
   printOn: file [^ file << self prefix << ')']
   interp []
].


" Given "
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


"changed line 364-365"
MiniBasic subclass: Interpreter [
   |statements|
   Interpreter class >> new: program [^ super new init: program]
   init: program [
      statements := Array new: program size.
      1 to: program size do: [:index|
         |stmt parsed label|
         stmt := (program at: index) at: 3.
         statements at: index put: (Stmt parse: stmt).
         label := (program at: index) at: 2.
         label ifNotNil: [Stmt addStmtLabel: label to: index].
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
      |stmtNr|
      [stmtNr := Stmt getStmtNr. stmtNr <= statements size]
      whileTrue: [
         |stmtObj|
         Stmt incrStmtNr.
         stmtObj := statements at: stmtNr.
         Debug > 1 ifTrue: 
                [stdout << stmtNr << ': ' << stmtObj << nl].
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

   Main class >> getopts [
      |fileName|
      Smalltalk arguments: '-d' do: [:opt :arg|
         opt = $d ifTrue: [Debug incr].
         opt = nil ifTrue: [
            fileName isNil ifFalse: [Main usage value].
            fileName := arg.
         ].
      ] ifError: [Main usage value].
      Debug > 0 ifTrue: [
         stdout << scriptName << ': ' << Smalltalk arguments << nl.
      ].
      ^ fileName.
   ]

   Main class >> main [
      |fileName|
      fileName := Main getopts.
      fileName isNil ifTrue: [Main usage value].
      [
         |program interpreter|
         FileStream fileIn: fileName.
         program := Program get.
         Debug > 0 ifTrue: [Main print: program].
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