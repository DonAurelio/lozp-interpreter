% Author: Paula Siaucho <pm.siaucho1305@uniandes.edu.co>
% Author: Aurelio Vivas <aa.vivas@uniandes.edu.co>
% Date: 07/05/2019

declare
Program = "
(defvar X)
(defun Fac (N)
(if (= N 0)
 (* N (Fac (- N 1) ) ) ) )
(unify X (Fact 5) )
"

% Atom: (str) -> str
% given an Text, it extract and return
% the nearest Atom 
fun {Atom Text}
   case Text of nil then nil
   [] H|T then
      % ' '
      if H == 32 then nil
      % '\n'
      elseif H == 10 then nil
      % '('
      elseif H == 40 then nil
      % ')'
      elseif H == 41 then nil
      else {Append [H] {Atom T}}
      end
   end
end

% Tests
{Browse {Atom "Hello)"}}  % "Hello"
{Browse {Atom "Hello "}}  % "Hello"
{Browse {Atom "Hello\n"}} % "Hello"
{Browse {Atom "(Hello"}}  % "", beacuse ( must be removed

% MoveFordward: (int * str) -> str
% Given a text, return a new text
% moved Times characters fordward
fun {MoveForward Times Text}
   if Times == 0 orelse Text == nil then Text
   else {MoveForward (Times - 1) Text.2} end
end

% Tests
{Browse {MoveForward 2 "Hello"}}  % "llo"
{Browse {MoveForward 6 "Hello"}}  % nil

% IsAlpha: (str) -> bool
% Chech if the Letter is an alphabetic.
% character.
fun {IsAlpha Letter}
   local Bool in
      if Letter == nil then
	 Bool = false
      else 
	 {Char.isAlpha Letter Bool}
      end
      Bool
   end
end

% Test
{Browse {IsAlpha "A".1}}  % true
{Browse {IsAlpha nil }}  % false
{Browse {IsAlpha "1".1}}  % false

% IsDigit: (str) -> bool
% Check if the given Letter is numeric.
fun {IsDigit Letter}
   local Bool in
      if Letter == nil then
	 Bool = false
      else
	 {Char.isDigit Letter Bool}
      end
      Bool
   end
end

% Test
{Browse {IsDigit "A".1}}  % false
{Browse {IsDigit nil }}  % false
{Browse {IsDigit "1".1}}  % true


% Lexer: Takes a String and return a list of tokens
% Text: Text to be tokenized
fun {Lexer Text}
   case Text of nil then nil
   [] H|T then
      % " "
      if H == 32 then {Lexer T}
      % "\n" 
      elseif H == 10 then {Lexer T}
      % "("
      elseif H == 40 then "("|{Lexer T}
      % ")"
      elseif H == 41 then ")"|{Lexer T}
      % "*"
      elseif H == 42 then "*"|{Lexer T}
      % "+"
      elseif H == 43 then "+"|{Lexer T}
      % "-"
      elseif H == 45 then "-"|{Lexer T}
      % "="	 
      elseif H == 61 then "="|{Lexer T}
      % digits and letter
      elseif {IsDigit H} orelse {IsAlpha H} then
	 local
	    Atm = {Atom  Text}
	 in
	    Atm|{Lexer {MoveForward {Length Atm} Text}}
	 end 
      else {Browse "Unknown character"} nil end
   end
end

% Tests
{Browse {Lexer Program}}
{Browse 'Finish'}
