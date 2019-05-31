% Author: Paula Siaucho <pm.siaucho1305@uniandes.edu.co>
% Author: Aurelio Vivas <aa.vivas@uniandes.edu.co>
% Date: 07/05/2019


declare
% Main test program with recursion
PROGRAM_1 =
[
 ["defvar" "X"]
 ["defun" "Fac" [ "N" ]
  [
   ["conditional" ["=" "N" "0"] "1" ["multiply" "N" ["Fac" ["substract" "N" "1"]]] ]
  ]
 ]
 ["Fac" "5"]
 ["unify" "X" [ "Fac" "5"]]
]

% Testing expressions in general
PROGRAM_2 =
[
 "1" 
 "20" 
 "true" 
 ["sum" "20" ["multiply" "10" "1"]]
 ["=" "1" "1"]  
 ["defvar" "Y"] 
 "Y"
 ["unify" ["multiply" "20" "4"] "Y"]
 "Y"
 ["defun" "Hola" ["H"] ["H"]]
 ["Hola" "1"]
 ["conditional" ["=" "1" "0"] "0" ["multiply" "2" "4"]]
]

% Testing functions variables scoping and closure
PROGRAM_3 = 
[
 ["defvar" "X"]
 ["unify" "X" "5"]
 ["defun" "A" nil ["X"]]
 ["defun" "B" nil [ ["defvar" "X"] ["A"] ]]
 ["B"]
]

%_____________________________________________ CONTEXT ___________________________________________

% initial context
CTX = env(env:nil)

% ApplyCtx: (str * record) -> value
% Identifier: A variable or procedure name.
% Ctx: A mapping from identifiers to values.
% Return the value of an identifier from the context.
% If the identfiier is not in the context raises and error.
fun {ApplyCtx Identifier Ctx}
   case Ctx
   of nil then
      {Browse Identifier}
      {Exception.'raise' 'Identifier not found'#Identifier} nil
   else
      local
	 Field = {String.toAtom Identifier}
	 Result = {Value.condSelect Ctx Field nil}
      in
	 if {Not {IsDet Result}} then 
	    'undetermined'
	 elseif Result == nil then
	    {ApplyCtx Identifier Ctx.env}
	 else
	    Result
	 end
      end
   end
end

% ExistsIdentCtx: (str * record) -> bool
% Return true if the Identifier is defined in the current
% context Ctx.
fun {ExitsIdetCtx Identifier Ctx}
   case Ctx
   of nil then false
   else
      local
	 Field = {String.toAtom Identifier}
	 Result = {Value.condSelect Ctx Field nil}
      in
	 if {Not {IsDet Result}} then true
	 elseif Result == nil then false
	 else true end
      end
   end
end

% AddIdentCtx: (str * record) -> record
% Return a new context where the new Identifier
% is declared.
fun {AddIdentCtx Identifier Ctx}
   local
      Field = {String.toAtom Identifier}
      Test = {ExitsIdetCtx Identifier Ctx}
   in
      if Test then 
	 {Exception.'raise' 'AddIdentifierCtx: Identifier already defined.'#Field} nil
      else {Record.adjoin Ctx env(Field:_)} end
   end
end

% AddIdentsCtx: (list-of-str * record) -> record
% Return a new context where the list of identifiers
% are declared.
fun {AddIdentsCtx Identifiers Ctx}
   case Identifiers
   of nil then Ctx
   [] H|T then {AddIdentsCtx T {AddIdentCtx H Ctx}}
   end
end

% SetIdentCtx: (str * int|bool|closure) -> int|bool|closure
% Unifies the variables identifier with the value (Val) in the
% current context.
fun {SetIdentCtx Identifier Val Ctx}
   case Ctx
   of nil then
      {Browse Identifier}
      {Exception.'raise' 'SetIdentCtx: Identifier not found'#Identifier} nil
   else
      local
	 Field = {String.toAtom Identifier}
	 Result = {Value.condSelect Ctx Field nil}
      in
	 if {Not {IsDet Result}} then 
	    Ctx.Field = Val
	    Val
	 elseif {IsDet Result} then
	    {Exception.'raise' 'SetIdentCtx: Identifier already has a value'#Identifier#Result} nil
	 else
	    {Exception.'raise' 'SetIdentCtx: Identifier is not in the current context'#Identifier} nil
	 end
      end
   end
end

% SetIdentsCtx: (list-of-str * list-of-int|bool|closure) -> int|bool|closure
% Unifies the list of identifiers with the list of values (Vals) in the
% Curren context
fun {SetIdentsCtx Identifiers Vals Ctx}
   local
      fun {SetIdents Ct Index}
	 if Index == 1 then
	    {SetIdentCtx Identifiers.Index Vals.Index Ct}
	 else
	    local Value in
	       Value = {SetIdentCtx Identifiers.Index Vals.Index Ct}
	       {SetIdents Ct (Index - 1)}
	    end
	 end
      end
   in
      {SetIdents Ctx {List.length Identifiers}}
   end
end

% ExtendCtx: (record) -> record
% Extend the current context, return a
% new extended context.
fun {ExtendCtx Ctx}
   env(env:Ctx)
end

%_____________________________________________ HELPERS  ___________________________________________

% Arity: (list * int) -> bool
% Check if Args has the passed arity.
fun {Arity Args Arity}
   {List.length Args} == Arity
end

% All: (fun * list) -> bool
% Check if all Args fullfit the predicate.
fun {All Predicate Args}
   case Args
   of nil then true
   [] H|T then
      if {Predicate H} then
	 {All Predicate T}
      else false
      end
   end
end

fun {IsIdentBound Identifier Ctx}
   case {ApplyCtx Identifier Ctx}
   of 'undetermined' then false
   else true
   end
end

%________________________________________ EXPRESSION PREDICATES ____________________________________

% IsIntExp: (str) -> bool
% Check if an str represents an integer type
fun {IsIntExp Exp}
   {String.is Exp} andthen {String.isInt Exp}
end

% IsBoolEx: (str|list) -> bool
% Check if Exp represents a boolean expression
% "true", "false" and [">" "1" "2"] are bool expressions.
fun {IsBoolExp Exp}
   case Exp
   of "true" then true
   [] "false" then true
   else false
   end
end

% IsCompExp: (str|list) -> bool
% Check if Exp represents a comparison expression
% Example:
% [">" "1" "2"], true
% ["fac" "1"], false
% ["<=" "1" "2"], true
fun {IsCompExp Exp}
   case Exp
   of H|T then
      if H == ">" then true
      elseif H == "<" then true
      elseif H == "=" then true
      elseif H == ">=" then true
      elseif H == "<=" then true
      else false
      end
   else false
   end
end

% IsAppExp: (str|list) -> bool
% Check if Exp represents a procedure application.
% Example:
% [+ "1" "2"] false, its an arithmetic expression
% ["Fact" "N" [+ "3" "4"]] true
fun {IsAppExp Exp}
   {List.is Exp}
   andthen {IsIdentExp Exp.1}
end

% IsArithExp: (str|list) -> bool
% Check if Exp reprsents an arithmetic expressios.
fun {IsArithExp Exp}
   if {List.is Exp} then
      case Exp
      of nil then false
      [] H|T then
	 if H == "sum" then true
	 elseif H == "substract" then true
	 elseif H == "multiply" then true
	 else false
	 end
      else false
      end
   else false
   end
end

% IsIdentExp: (str|list) -> bool
% Check if Exp is an identifier (variable).
fun {IsIdentExp Exp}
   case Exp
   of H|T then
      if {Char.is H} then 
	 {Char.isUpper H}
      else false end
   else false
   end
end

% IsDefVarExp: (str|list) -> bool
% Check if Exp represents a variable definition expression
% Example:
% [defvar X], true.
% [defvar], false.
% [defvar "x"], false.
% [Defvar "X"], false.
fun {IsDefVarExp Exp}
   {List.is Exp}
   andthen (Exp.1 == "defvar")
   andthen {Arity Exp 2}
   andthen {IsIdentExp Exp.2.1}
end

% IsUnifyExp: (str|list) -> bool
% Check if Exp represents a unification expression
% Example:
% "A", false
% ["unify" "X"], false.
% ["unify" "X" ["Fact" "4"]], true.
fun {IsUnifyExp Exp}
   {List.is Exp}
   andthen (Exp.1 == "unify")
   andthen {Arity Exp 3}
end

% IsDefunExp: (str|list) -> bool
% Check if the given expression represents
% a function definition.
fun {IsDefunExp Exp}
   {List.is Exp}
   andthen {Arity Exp 4}
   andthen (Exp.1 == "defun")
   % The name of the function is an identifier.
   andthen {IsIdentExp Exp.2.1}
   % Parameters are in a list.
   andthen {List.is Exp.2.2.1}
   % Function body is a list
   andthen {List.is Exp.2.2.2.1}
end

% IsConditionalExp: (str|list) -> bool
% Check if the given expression represents
% a conditional.
fun {IsConditionalExp Exp}
   {List.is Exp}
   andthen {Arity Exp 4}
   andthen (Exp.1 == "conditional")
   andthen {IsCompExp Exp.2.1}
end

%_____________________________________________ EVAL EXPRESSIONS ______________________________________

% EvalExps: (list-of-str|list * record * int|bool|closure|env) -> int|bool|closure|env
% Eval a list of expressions. Return the value of the
% last evaluated expression.
% Example:
% A list of expressions is ["1" "2" ["devar" X]] where
% "1", "2", and ["devar" X] are expressions.
% Note:
% the result of evaluate a list of expression is to return
% the result of the last expression in the list.
% When a defvar expression is encounter, the rest of the
% expressions must be evaluated in the new context that
% has the new variable defined by the defvar expression.
% the same case applies for functions definitions.
fun {EvalExps Exps Ctx Result}
   case Exps
   of nil then Result
   [] H|T then
      if {IsDefVarExp H} then
	 local NewCtx = {EvalExp H Ctx} in
	    {EvalExps T NewCtx NewCtx}
	 end
      elseif {IsDefunExp H}then
	 local NewCtx = {EvalExp H Ctx} in
	    {EvalExps T NewCtx NewCtx}
	 end
      else {EvalExps T Ctx {EvalExp H Ctx}} end      
   else {Exception.'raise' 'EvalExps: Is not a list expression.'#Exps} nil
   end
end

% EvalExp: (str|list * record) -> int|bool|closure|env
% Return the value of an evaluated expression.
fun {EvalExp Exp Ctx}
   if {IsIntExp Exp} then {String.toInt Exp} 
   elseif {IsBoolExp Exp} then {String.toAtom Exp}
   elseif {IsCompExp Exp} then {EvalCompExp Exp Ctx}
   elseif {IsArithExp Exp} then {EvalArithExp Exp Ctx}
   elseif {IsIdentExp Exp} then {ApplyCtx Exp Ctx}
   elseif {IsDefVarExp Exp} then {EvalDefVarExp Exp Ctx}
   elseif {IsUnifyExp Exp} then {EvalUnifyExp Exp Ctx}
   elseif {IsDefunExp Exp} then {EvalDefunExp Exp Ctx}
   elseif {IsAppExp Exp} then {EvalAppExp Exp Ctx}
   elseif {IsConditionalExp Exp} then {EvalConditionalExp Exp Ctx}
   else {Browse Exp}{Exception.'raise' 'EvalExp: Unkonwn expression.'#Exp} nil
   end
end

% EvalArgs: (list-of-exp * context) -> list-of-values
% Evaluate each expression on the list. It is
% used to evaluate funtion arguments expressions.
fun {EvalArgs Exps Ctx}
   case Exps
   of nil then nil
   [] H|T then
      {EvalExp H Ctx}|{EvalArgs T Ctx}
   end
end

% EvalArithExp: (list * record) -> int
% Evaluate arithmetic expressions in the
% current context (environment).
fun {EvalArithExp Exp Ctx}
   case Exp
   of H|T then
      local Args = {EvalArgs T Ctx} in
	 {ApplyArithOp H Args}
      end
   else
      {Exception.'raise' 'EvalArithExp: Exp is not Arithmetic.'} nil
   end
end

% EvalCompExp: (list * record) -> bool
% Evaluate boolean expressions in the
% current context.
fun {EvalCompExp Exp Ctx}
   case Exp
   of H|T then
      local Args = {EvalArgs T Ctx} in
	 {ApplyCompOp H Args}
      end       
   else
       {Exception.'raise' 'EvalCompExp: Exp is not a comparison  operation.'} nil
   end
end

% EvalDefVarExp: (list * record) -> record
% Evaluate variable definition expresion.
% return a new context with the new variable
% defined.
fun {EvalDefVarExp Exp Ctx}
   local Defvar = Exp.1 Identifier = Exp.2.1 in
      {AddIdentCtx Identifier Ctx}
   end
end

% EvalUnifyExp: (str|list * record) -> int|bool|closure|env
% Perform the unification algorthm. Return the value which
% variable names or values where unified.
fun {EvalUnifyExp Exp Ctx}
   local
      Exp1 = Exp.2.1
      Exp2 = Exp.2.2.1
   in
      % Case 1: Both expresions are identifiers
      if {IsIdentExp Exp1} andthen {IsIdentExp Exp2} then
         % A: Both identifiers are bound they must to have the same value.
	 if {IsIdentBound Exp1 Ctx} andthen {IsIdentBound Exp2 Ctx} then
	    {ApplyUnifyValues {ApplyCtx Exp1 Ctx} {ApplyCtx Exp2 Ctx}}
         % B: Both identifiers are unbound so they must have the same value.
	 elseif {Not {IsIdentBound Exp1 Ctx}} andthen {Not {IsIdentBound Exp2 Ctx}} then
	    {ApplyUnifyValues {ApplyCtx Exp1 Ctx} {ApplyCtx Exp2 Ctx}}
	 % C: The fist identifier is unbound and the second one is bound,
	 % the first identifier takes the value of the second one.
	 elseif {Not {IsIdentBound Exp1 Ctx}} andthen {IsIdentBound Exp2 Ctx} then
	    {ApplyUnifyIdent Exp1 {ApplyCtx Exp2 Ctx} Ctx}
	 % D: The second identifier is unbound and the first one is unbound,
	 % the second identifier takes the value of the first one.
	 elseif {IsIdentBound Exp1 Ctx} andthen {Not {IsIdentBound Exp2 Ctx}} then
	    {ApplyUnifyIdent Exp2 {ApplyCtx Exp1 Ctx} Ctx}
	 end
      % Case 2: The fist expression is an idetifier an the second one is not.
      elseif {IsIdentExp Exp1} andthen {Not {IsIdentExp Exp2}}  then
	 % A: If the identifier is bound, then, it unifies with the Exp2 if they have the same value
	 if {IsIdentBound Exp1 Ctx} then
	    {ApplyUnifyValues {ApplyCtx Exp1 Ctx} {EvalExp Exp2 Ctx}}
	 % B: If the identifier is unbound, then, it will be assigned to the Exp2's value 
	 else
	    {ApplyUnifyIdent Exp1 {EvalExp Exp2 Ctx} Ctx}
	 end
       % Case 3: The first expression  is not an indentifer and the second one is.
       elseif {Not {IsIdentExp Exp1}} andthen {IsIdentExp Exp2} then
	 % A: If the identifier is bound, then, it unifies with the Exp1, if they have the saeme value
	 if {IsIdentBound Exp2 Ctx} then
	    {ApplyUnifyValues {ApplyCtx Exp2 Ctx} {EvalExp Exp1 Ctx}}
	 % B: If the identifier is unbound, then, it will be assigned to the Exp1's value 
	 else
	    {ApplyUnifyIdent Exp2 {EvalExp Exp1 Ctx} Ctx}
	 end
      else
	 {ApplyUnifyValues {EvalExp Exp1 Ctx} {EvalExp Exp2 Ctx}}
      end
   end
end

% EvalDefunExp: (list * record) -> record
% Define a function in the current context,
% return the context with the new function
% defined.
fun {EvalDefunExp Exp Ctx}
   local Params Body Identifier Fun Ctx1 Ctx2 Value in      
      Identifier=Exp.2.1
      Params=Exp.2.2.1
      Body=Exp.2.2.2.1
      Ctx2 = {AddIdentCtx Identifier Ctx}
      Fun=closure(name:Identifier params:Params body:Body ctx:Ctx2)
      Value = {SetIdentCtx Identifier Fun Ctx2}
      Ctx2
   end
end

% EvalAppExp: (list * record) -> int|bool|closure|env
% Perform the evaluation of a function application
% expression in the current context.
fun {EvalAppExp Exp Ctx}
   local
      Identifier
      Args
      Values
      Function
      Ctx0
      Ctx1
      Ctx2
      Ctx3
   in
      Identifier = Exp.1
      Args = Exp.2
      Function = {ApplyCtx Identifier Ctx}
      if {Arity Function.params {List.length Args}} then  
	 if {List.length Function.params} == 0 then
	    Ctx0 = {ExtendCtx Function.ctx}
	    {EvalExps Function.body Ctx0 nil}
	 else
	    Values = {EvalArgs Args Ctx}
	    Ctx1 = {ExtendCtx Function.ctx}
	    Ctx2 = {AddIdentsCtx Function.params Ctx1}
	    Ctx3 = {SetIdentsCtx Function.params Values Ctx2}
	    {EvalExps Function.body Ctx2 nil}
	 end
      else
	 {Exception.'raise' 'EvalUnifyIdent: Exp is not a unification operation.'#Exp} nil
      end
   end
end

% EvalConditionalExp: (list * record) -> int|bool|closure|env
% Perform the evaluation of conditional expression in the
% current context.
fun {EvalConditionalExp Exp Ctx}
   local
      TestExp = Exp.2.1
      ThenExp = Exp.2.2.1
      ElseExp = Exp.2.2.2.1
      Test = {EvalExp TestExp Ctx}
   in
      if Test then {EvalExp ThenExp Ctx} else {EvalExp ElseExp Ctx} end
   end
end

%___________________________________________ APPLY HELPERS  ________________________________________

% ApplyUnifyValues: (int|bool|closure * int|bool|closure) -> int|bool|closure
% delegate values unification to Mozart/Oz.
fun {ApplyUnifyValues Value1 Value2}
   Value1 = Value2
end

% ApplyUnifyIdent: (str * int|bool|closure * record) -> int|bool|closure
% Unifies an indetifier with a value
% in the current context
fun {ApplyUnifyIdent Identifier Value Ctx}
   {SetIdentCtx Identifier Value Ctx}
end

% ApplyArithOp: (str * list-of-int) -> int
% Perform the basic arithmetic operations.
fun {ApplyArithOp Op Args}
   if {All IsInt Args} then
      case Op
      of "sum" then Args.1 + Args.2.1
      [] "substract" then Args.1 - Args.2.1
      [] "multiply" then Args.1 * Args.2.1
      else {Exception.'raise' 'EvalArithExp: Arithmetic operation not known.'} nil
      end
   else
      {Exception.'raise' 'EvalArithExp: Arity or Type erro.'#Args } nil
   end
end

% ApplyCompOp: (str * list-of-int) -> bool
% Perform the basic comparison operations
fun {ApplyCompOp Op Args}
   if {Arity Args 2} andthen {All IsInt Args} then
      case Op
      of ">" then Args.1 > Args.2.1
      [] "<" then Args.1 < Args.2.1
      [] "="  then Args.1 == Args.2.1
      [] ">=" then Args.1 > Args.2.1 orelse Args.1 == Args.2.1
      [] "<=" then Args.1 > Args.2.1 orelse Args.1 == Args.2.1
      else {Exception.'raise' 'EvalArithExp: Comparison operation not known.'} nil
      end
   else
      {Exception.'raise' 'ApplyComOp: Arity or Type error.'} nil
   end	
end


{Browse {EvalExps PROGRAM_1 CTX nil}}
{Browse 'Finish'}
