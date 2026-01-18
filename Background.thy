theory Background
  imports Main 
begin 

(* subsection\<open>Types, terms and function \label{background}\<close> *)
subsection \<open>Isabelle/HOL \label {isabelle}\<close>
text \<open>Isabelle/HOL \cite{nipkow2002isabelle} is a proof assistant, 
a computer program that assists in conducting proofs of theorems using higher-order logic. 
It is being developed at the University of Cambridge and Technische Universität München. 
Isabelle/HOL gives the languages for mathematical reasoning and the rules similar to 
natural deduction's rules to carry out proofs. 
We can utilize Isabelle/HOL to show mathematical proofs and reason and prove 
the semantics of a programming language and its properties. 
Isabelle/HOL developments comprise a list of theories, the definition of functions, types, sets, 
and a set of lemmas, theorems, and so forth, interpreted by the theorem prover. 
It also provides two ways of writing proofs: (1) a tactic script and 
(2) a structured proof language called Isar (Intelligible Semi-Automated Reasoning). 
In this thesis, we frequently shift between tactic script and Isar to produce proofs of lemmas. 

Furthermore, Isabelle/HOL supplies us with three means to validate whether our theories or lemmas are correct or not. 
These are, respectively, counter-example commands, tactics, and inference tools. 
The commands \textbf{quickcheck} and \textbf{nitpick} are used to search for and generate counter-examples. 
Tactics include \textbf{auto} and \textbf{metis} and assist us in proving specific goals automatically. 
Other automated tools, such as \textbf{sledgehammer} 
or \textbf{solve\_direct}, help us create proofs for the current goal by recommending tactics. \<close>

text \<open>We now provide in detail the necessary technical background on Isabelle/HOL to 
understand this thesis's remainder. First, we want to talk about \textbf{Types}.
They are
(1) \textbf{basic types}, in particular @{term nat}, the type of natural numbers, 
(2) \textbf{type constructors}, particularly  @{term list}, the type of lists, 
(3) \textbf{arbitrary types} represented by variable (denoted by @{text "'a"}), 
(4) \textbf{recursive types} represented by the @{term datatype} command introducing recursive data types. 


Moreover, the keyword @{term typedecl} describes a new type name without any
additional assumptions, e.g., @{text "typedecl FieldName"} describes
a set of field names @{term FieldName}. 
Besides, the keyword @{term type_synonym} introduces a synonym for the type specified, 
e.g., @{text "type_synonym Identifier = nat"} introduces a 
synonym @{term Identifier} for the type of natural number @{term nat}. 
Datatype @{term option} is used to add a new element @{term None} 
to an existing type @{text "'a"}. For instance, in this thesis, 
we usually use the @{term option} type to represent partial functions. 
In particular, the partial function from @{term a} to @{term b} 
is represented by the type @{text "a \<Rightarrow> b option"}.\<close>

text \<open>Second, we speak about \textbf{Terms}: 
(1) \textbf {function application} @{term "f t"} is the call function @{term f} 
with @{term t} is an argument, 
(2) \textbf {function abstraction} @{term "\<lambda>x. t"} is the function, where @{term x} is a parameter 
and returning value @{term t}. \<close>

text \<open>The third is a \textbf{definition}, also called a non-recursive definition.
It is defined as a @{text "definition"} command, for instance, @{term inc} as follows. \<close>

definition inc:: "nat \<Rightarrow> nat" 
  where 
"inc n = n + 1"

text \<open>Besides, we use the \textbf{recursive function} in this thesis.
We most use two common ways to define a recursive function: (1) 
@{text fun} defines a more expressive function, 
and we might need to prove termination manually, 
and (2) @{text primrec}, a restrictive version of @{text fun}, defines 
a recursive function in which we need to state every rule. 
Furthermore, the \textbf{inductive} definition is essential. 
Thus, it is the key construct of operational semantics in the next part of the thesis. \<close>

text \<open>Forth, \textbf{records} are used in the thesis, generalizing tuples' concept, 
but their components have names instead of position.
A @{text record} declaration introduces new types and types of abbreviations.
For example, the record of type @{text pt} represents a point 
in three-dimensional space, in which three fields named @{term x}, 
@{term y}, and @{term z} of type @{term int}. \<close>

record pt = x :: int y :: int z :: int 

text\<open>Finally, as we mentioned earlier, in this thesis, 
there are two ways of writing proofs: a tactic script and an Isar. 
Let us give a glimpse at both of them. 
A tactic script, called "apply" style proofs, is backward reasoning, progressing from goal to premises. 
On the other hand, Isar appears like a mathematical reasoning style with structured proofs and similar notations 
such as @{term assume}, @{term have}, @{term thus}, and @{term hence}.
 
We give a toy example that proves @{text "P \<and> Q \<longrightarrow> Q \<and> P"}, to say the difference between "apply" and Isar.\<close>

text \<open>In the first one @{text "applyStyle"} utilizing the @{text "apply"} tactic, 
the audience will probably face difficulty 
to read since the proof does not show the result of each step.\<close> 

lemma applyStyle: "P \<and> Q \<longrightarrow> Q \<and> P" 
  apply (rule impI)
  apply (rule conjI)
   apply (rule conjunct2)
   apply assumption
  apply (rule conjunct1)
  apply assumption
  done

text \<open>On the other hand, the second one, @{text "IsarStyle"}, is more structured and readable.
Similar to the mathematical language, we want to show intermediate steps as statement @{text "G1"} and statement @{text "G2"}. 
Then, from these intermediate steps, we can prove the ultimate goal. \<close>

lemma IsarStyle: "P \<and> Q \<longrightarrow> Q \<and> P"
proof 
  assume H: "P \<and> Q"
  from H have G1: "P" 
    by (rule conjunct1)
  from H have G2: "Q"
    by (rule conjunct2)
  from G2 and G1 show "Q \<and> P"
    by (rule conjI)
qed
end