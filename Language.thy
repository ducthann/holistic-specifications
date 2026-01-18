theory Language
  imports Support 
begin
section \<open>Language Syntax \label{langsyntax}\<close>
text\<open>
In the first part of the formalization, we give the language syntax of underlying object-oriented programming and 
its operational semantics and connect other modules to the module under consideration. 
We formalize all of them in Isabelle/HOL. 
Firstly, we are required to formalize the syntax of the language.
We present them by a given set of program variables @{term Identifier}, 
a set of field names @{term FieldName}, a set of class names @{term ClassName}, 
and a set of method names @{term MethodName}. 
The fields of the language declared are untyped, the method consists of an untyped parameter, with
no return type as well, because the core language of Holistic specifications is untyped. \<close>

type_synonym Identifier = nat
typedecl FieldName
typedecl ClassName
typedecl MethodName

text\<open> Statements @{term Stmt} in the programming language consist of field read @{term ReadFromField}, 
field write @{term AssignToField}, method call  @{term MethodCall}, 
object creation @{term NewObject}, and return statement  @{term Return}. \<close>

datatype Stmt = AssignToField FieldName Identifier (* this.FieldName := Identifier *) 
              | ReadFromField Identifier FieldName (* Identifier := this.Fieldname *) 
              | MethodCall Identifier Identifier MethodName "Identifier list" (*Identifier := Identifier.MethodName(Identifier list) *)            
              | NewObject Identifier ClassName "Identifier list" (*Identifier := new ClassName (Identifier list) *)
              | Return Identifier (*return Identifier *)

text \<open>The sequences of a statement are declared as @{term Stmts} as well. 
It consists of a single statement and a sequence of statements.\<close>
datatype Stmts = SingleStmt Stmt | Seq Stmt Stmts

text \<open>The method body consists of sequences of statements 
and their parameters, which are a list of identifiers.
Notice that we store the method names inside the class to make lookup easier. \<close>

record Method =  formalParams :: "Identifier list"
                 body :: Stmts

text \<open>The class description consists of field and method declarations.
Note that we omit the @{term ClassId} as it appears to be duplicated in the @{term Module}.
We also assume that every method is defined on every object for the sake of simplicity. \<close>

record Class =   objFields :: "FieldName list"
                 methods   :: "MethodName \<Rightarrow> Method"

text\<open>A module is defined as the set of mappings from class names to class descriptions. 
Note that the class name is distinct from local variables. 
Every class is not defined by every module, as otherwise linking becomes meaningless.\<close>
(* We cannot pretend that every class is defined by every module, as otherwise linking becomes meaningless.  *)
type_synonym Module  = "ClassName \<Rightarrow> Class option"

text\<open>Method lookup function @{term \<M>} returns a method @{term m} for a class @{term C} inside the module @{term M}.\<close>
(* Lookup a method @{term m} for a class @{term C} inside module @{term M} *)
definition 
\<M> :: "Module \<Rightarrow> ClassName \<Rightarrow> MethodName \<Rightarrow> Method option"
  where
"\<M> M C m \<equiv> case (M C) of None \<Rightarrow> None | Some c \<Rightarrow> Some ((methods c) m)"

section \<open>Operational Semantics of the Language \label{opsemantics}\<close>
subsection\<open>Interpretations\<close>
text\<open> Heaps @{term \<chi>} are mappings from addresses @{term \<alpha>} to objects @{term obj}. 
Stack frames @{term \<phi>} are mappings from identifiers @{term x} plus the distinguished identifier @{term this} to values, 
where values include addresses. 
Stack frames also store the current continuation (code to be executed). \<close>
 
text \<open>Configurations @{term \<sigma>} are pairs @{term "(\<psi>,\<chi>)"} 
where @{term \<psi>} is a list of stack frames @{term \<phi>} and @{term \<chi>} is the heap.\<close>

text\<open> The following notation we use throughout the upcoming sections.
\begin{itemize}
  \item Lookup of fields @{term f} on object with address @{term \<alpha>} in the heap @{term \<chi>}, @{term "field_lookup \<chi> \<alpha> f"}, is written @{text "\<chi>(\<alpha>, f)"}.
  \item The class of the object whose address is @{term \<alpha>} in heap @{term \<chi>}, @{term "class_lookup \<chi> \<alpha>"}, is written @{text "Class(\<alpha>)\<^bsub>\<chi>\<^esub>"}.
  \item Lookup of the class of the @{term "this"} object in the runtime configurations @{term \<sigma>}, \\ @{term "this_class_lookup \<sigma>"}, is written @{text "Class(this)\<^bsub>\<sigma>\<^esub>"}.
  \item Lookup of identifier @{term x} in the frame @{term \<phi>}, @{term "ident_lookup \<phi> x"}, is written @{text "\<lfloor>x\<rfloor>\<^bsub>\<phi>\<^esub>"}.
  \item Lookup of identifier @{term x} in context @{term \<sigma>}, @{term "evalVar x \<sigma>"}, is written @{text "\<lfloor>x\<rfloor>\<^bsub>\<sigma>\<^esub>"}.
  \item Lookup of field @{term f} from @{term "this"} object in frame @{term \<phi>} and heap @{term \<chi>}, @{term "this_field_lookup \<phi> \<chi> f"}, is written @{text "\<lfloor>this.f\<rfloor>\<^bsub>(\<phi>,\<chi>)\<^esub>"}.
  \item Update the variable map of frame @{term \<phi>} so that variable @{term x} maps to value @{term v},\\ @{term "frame_ident_update \<phi> x v"}, is written @{text "\<phi>[x \<mapsto> v]"}.
  \item Update the object at address @{term \<alpha>} on the heap @{term \<chi>} to the object @{term obj}, @{term "heap_update \<chi> \<alpha> obj"}, is written @{text "\<chi>[\<alpha> \<mapsto> obj]"}.
  \item To obtain the continuation @{term cont} from the frame @{term \<phi>}, we write @{term "cont \<phi>"}.   
  \end{itemize} \<close>

subsection\<open>Runtime Entities\<close>
text\<open>We are ready to introduce the addresses @{term Addr} as an enumerable set and null @{term Null}.\<close>
(* Addresses *)
type_synonym Addr = nat
consts Null :: Addr

text\<open>Then, we also define values @{term Values}, consisting of null, addresses, and sets of addresses @{term VAddrSet}.\<close>

datatype Value = VAddr Addr | VAddrSet "Addr set"

text\<open>Continuations are either statements or a nested call followed by statements. 
Frames consist of a continuation, a mapping from identifiers to values, and an address @{term this}.\<close>
(* Continuations, aka Code Stubs *)
datatype Continuation = Code Stmts | NestedCall Identifier Stmts  (* x := \<bullet> ; Stms *) 
(* Stack Frames *)
record Frame =  cont :: Continuation
                vars :: "Identifier \<Rightarrow> Value option" 
                this :: Addr

text\<open>Stacks are sequences of frames. Objects consist of a class identifier @{term className}
and a mapping from field name @{term FieldName} to values @{term values}. 
Heaps @{term Heap} are defined as mappings from addresses to objects.  
Lastly, runtime configurations @{term Config} are pairs of stacks and heaps. \<close>

text\<open> We use the option type to represent partial functions. i.e., the partial
function from @{term a} to @{term b} is represented by the type @{text "a \<Rightarrow> b option"}. 
For instance, the @{term objFields} is a partial function from @{term FieldName} to @{term Value} defined below.\<close>

type_synonym Stack = "Frame list"
record Object = className :: ClassName
                objFields :: "FieldName \<Rightarrow> Value option"
type_synonym Heap = "Addr \<Rightarrow> Object option"
type_synonym Config = "Stack \<times> Heap"

subsection\<open>Lookup and update of runtime configurations\<close>
text\<open>We represent interpretations of a field lookup and a class lookup.
The @{term field_lookup} function is used to retrieve the value stored in field
@{term f} of the object at address @{term \<alpha>} in the heap @{term \<chi>}. 
It is a partial function since there might be no such object at address
@{term \<alpha>}.\<close>

fun 
field_lookup :: "Heap \<Rightarrow> Addr \<Rightarrow> FieldName \<Rightarrow> Value option"
  where
"field_lookup \<chi> \<alpha> f = 
        (case (\<chi> \<alpha>) of None \<Rightarrow> None 
                     | Some obj \<Rightarrow> (objFields obj) f)"

text\<open>The function @{term class_lookup} is used to retrieve the class of the object @{term obj}
whose address is @{term \<alpha>} in the heap @{term \<chi>}. 
It is a partial function since there might be no such class at address @{term \<alpha>}.\<close>
(* class_lookup \<chi> a *)
fun 
class_lookup :: "Heap \<Rightarrow> Addr \<Rightarrow> ClassName option"
  where
"class_lookup \<chi> \<alpha> = 
        (case (\<chi> \<alpha>) of None \<Rightarrow> None 
                     | Some obj \<Rightarrow> Some (className obj))"

text\<open>The function @{term ident_lookup} is used to retrieve identifier @{term x} in the frame @{term \<phi>}.
It is a partial function since there might be no such identifier in the frame @{term \<phi>}.\<close>
(* identifier_lookup \<lfloor>x\<rfloor>\<phi> = \<phi>(x) *)
fun 
ident_lookup :: "Frame \<Rightarrow> Identifier \<Rightarrow> Value option"
  where
"ident_lookup \<phi> x = vars \<phi> x"

text\<open>The function @{term this_field_lookup} is used to retrieve the class of the @{term this} object
in the runtime configuration @{term \<sigma>}. 
It is a partial function since there might be no such class in the runtime configuration @{term \<sigma>}.\<close>
(* lookup a field of the 'this' object \<lfloor>this.f\<rfloor>\<^bsub>(\<phi>,\<chi>)\<^esub> *)
fun 
this_field_lookup :: "Frame \<Rightarrow> Heap \<Rightarrow> FieldName \<Rightarrow> Value option"
  where
"this_field_lookup \<phi> \<chi> f =  
    (case \<chi> (this \<phi>) of None \<Rightarrow> None 
                  | Some obj \<Rightarrow> objFields obj f)"

text\<open> 
The auxiliary function @{term this_field_update} is used to update the field @{term f}
of the distinguished @{term this} object to refer to value @{term v}, 
given the stack frame @{term \<phi>} and heap @{term \<chi>}.\<close>
(* upate a field of the 'this' object. Returns option since the lookup of 'this' in the heap might fail *)
fun 
this_field_update :: "Frame \<Rightarrow> Heap \<Rightarrow> FieldName \<Rightarrow> Value \<Rightarrow> Heap option"
  where
"this_field_update \<phi> \<chi> f v =
    (case \<chi> (this \<phi>) of None \<Rightarrow> None 
                  | Some obj \<Rightarrow> Some (\<chi>(this \<phi> := 
            Some (obj\<lparr>objFields := ((objFields obj)(f := Some v))\<rparr>))))"
 (* \<phi>[x \<mapsto> v] *)
text \<open>The function @{term frame_ident_update} updates the variable map of the stack frame @{term \<phi>} 
so that variable @{term x} maps to value @{term v}. \<close>

fun 
frame_ident_update :: "Frame \<Rightarrow> Identifier \<Rightarrow> Value \<Rightarrow> Frame"
  where
"frame_ident_update \<phi> x v = (\<phi>\<lparr>vars := ((vars \<phi>)(x := Some v))\<rparr>)"
(* \<chi>[a \<mapsto> o] *)

text \<open> The function @{term heap_update} updates the object at address @{term \<alpha>} 
on the heap @{term \<chi>} to map to the object @{term obj}. \<close>
fun 
heap_update :: "Heap \<Rightarrow> Addr \<Rightarrow> Object \<Rightarrow> Heap"
  where
"heap_update \<chi> \<alpha> obj = \<chi> (\<alpha> := Some obj)" 

text \<open> The function @{term this_class_lookup} is used to look up the class of the @{term this} object 
in the runtime configuration @{term \<sigma>}. \<close>
fun 
this_class_lookup :: "Config \<Rightarrow> ClassName option"
  where
"this_class_lookup \<sigma> =  
   (case \<sigma> of (\<phi>#\<psi>,\<chi>) \<Rightarrow>
       (case \<chi> (this \<phi>) of None \<Rightarrow> None 
                      | Some obj \<Rightarrow> Some (className obj))
           | _ \<Rightarrow> None)"

text \<open>Note that these above functions return @{term option} in case of lookup failure.\<close>

subsection\<open>Operational semantics \label{OpSemIsabelle}\<close>
text\<open>
Now, we turn to the operational semantics of the programming language. 
We define it as an inductive predicate called @{term exec}. 
Its rules make use of the following auxiliary definitions.\<close>
(* \<phi>'' = build_call_frame meth \<alpha> (map the paramValues)*)
text\<open>
The auxiliary function @{term build_call_frame} is used to create a new frame in which the @{term this} object 
is assigned by address @{term \<alpha>}, and each value also assigns each parameter of method @{term meth} in @{term paramValues}. 
We also need a condition that the length of method @{term meth} equals the length of the list @{term paramValues}.
We implement such a condition in the rule @{term exec_method_call}.\<close>

definition 
build_call_frame :: "Method \<Rightarrow> Addr \<Rightarrow> Value list \<Rightarrow> Frame" 
  where
"build_call_frame meth \<alpha> paramValues \<equiv> 
      \<lparr>cont = Code (body meth), 
       vars = map_of (zip (formalParams meth) paramValues),
       this = \<alpha>\<rparr>"

text\<open>
The auxiliary function @{term build_new_object} creates a new object in which 
each value in the list @{term fieldValues} assigns each field in class @{term c}.
Such a function is useful for the object creation's rule @{term exec_new}.
Same as the function @{term build_call_frame}, 
the length of both the list of fields in class @{term c} and the list @{term fieldValues} must equal.\<close>

definition 
build_new_object :: "ClassName \<Rightarrow> Class \<Rightarrow> Value list \<Rightarrow> Object"
  where
"build_new_object C c fieldValues \<equiv> 
      \<lparr>className = C, 
       objFields = map_of (zip (Class.objFields c) fieldValues)\<rparr>"

text\<open>In object creation's rule @{term exec_new}, we need a fresh address in heap @{term \<chi>}, i.e., 
the new address utterly different from addresses including the current heap @{term \<chi>}. 
The function @{term fresh_nat} generates such a fresh address.\<close>

definition 
fresh_nat :: "Identifier set \<Rightarrow> Identifier" 
  where
"fresh_nat X = (if X = {} then 0 else (Suc (last (sorted_list_of_set X))))"

text\<open>Lemma @{term fresh_nat_is_fresh} says that 
such a fresh address is not in the current heap @{term \<chi>}.\<close>
lemma fresh_nat_is_fresh [simp]:
  "finite X \<Longrightarrow> fresh_nat X \<notin> X"
  apply (induct rule: finite.induct) 
   apply simp
  apply(clarsimp simp: fresh_nat_def)
  using not_eq_a not_in_A by auto

text\<open>An operational semantics is represented as a set of rules given formally below.
These rules are method calls @{term exec_method_call}, variable assignment @{term exec_var_assign}, 
field assignment @{term exec_field_assign}, object creation @{term exec_new}, and return @{term exec_return}. \<close>

text\<open>The rule @{term exec_method_call} defines the semantics for method calls of the form
@{text "x := y.m(params)"}. It looks up in the current stack frame @{term \<phi>} the object @{term y} being invoked, 
producing the address @{term \<alpha>}, which is used to retrieve its class @{term C} from the heap @{term \<chi>}; the rule also
looks up each identifier in @{term params}, checking to make sure that each such lookup succeeds. 
The method name @{term m} of class @{term C} is looked up in the module @{term M} from which the new stack frame @{term \<phi>''} 
for the execution of the method is produced. 
The continuation is updated to remember that a nested call is being executed, whose result will be assigned to @{term x}.\<close>

text\<open>The rule @{term exec_var_assign} defines the semantics for field read of form @{text "x := this.y"}. 
The continuation is updated to remember that a sequence of statements @{term stmts} is being executed. 
The result of the lookup of the field @{term y} from @{term this} object in the frame @{term \<phi>} and the heap @{term \<chi>} 
will be assigned to @{term x}.\<close>

text\<open>The rule @{term exec_field_assign} defines the semantics for field write of form @{text "this.y = x"}.
The continuation is updated to remember that a sequence of statements @{term stmts} is being executed.
The rule looks up identifier @{term x} in the current stack frame @{term \<phi>}, producing the value @{term v}, which is updated to the field 
@{term y} to create a new heap @{term \<chi>'} given the stack frame @{term \<phi>} and heap @{term \<chi>}.\<close>

text\<open>The rule @{term exec_new} defines the semantics for object creation of form \\ @{text "x := new C(params)"}.
The rule looks up each identifier in @{term params}, checking to make sure that each such lookup succeeds. 
A fresh address @{term \<alpha>} will update the evaluation of identifier @{term x} in the current heap @{term \<sigma>}.
The heap @{term \<chi>} at the address @{term \<alpha>} will be updated by a new object, which each field declared in the method @{term m} 
of class @{term C} will be updated by each value of each identifier in @{term params}, respectively. \<close>

text\<open>The rule @{term exec_return} defines the semantics for the return statement of form @{text "return x"}. 
The value of identifier @{term x} in stack frame @{term \<sigma>} is assigned to 
the identifier @{term x'} where the result of a nested call is assigned.       
The continuation is updated to remember that a statement @{term  stmts'} followed by the nested call is being executed.\<close>

inductive
exec :: "Module \<Rightarrow> Config \<Rightarrow> Config \<Rightarrow> bool"  ("_, _ \<rightarrow>\<^bsub>e\<^esub> _")
  where 
exec_method_call: 
 "cont \<phi> = Code (Seq (MethodCall x y m params) stmts) \<Longrightarrow>
  ident_lookup \<phi> y = Some (VAddr \<alpha>) \<Longrightarrow>
  class_lookup \<chi> \<alpha> = Some C \<Longrightarrow>
  paramValues = map (ident_lookup \<phi>) params \<Longrightarrow>
  None \<notin> set paramValues \<Longrightarrow>
  \<M> M C m = Some meth \<Longrightarrow>
  length (formalParams meth) = length params \<Longrightarrow>
  \<phi>'' = build_call_frame meth \<alpha> (map the paramValues)  \<Longrightarrow>
  M, (\<phi> # \<psi>, \<chi>) \<rightarrow>\<^bsub>e\<^esub> (\<phi>'' # (\<phi>\<lparr>cont := NestedCall x stmts\<rparr>) # \<psi>, \<chi>)" | 

exec_var_assign:
 "cont \<phi> = Code (Seq (ReadFromField x y) stmts) \<Longrightarrow> 
  M, (\<phi> # \<psi>, \<chi>) \<rightarrow>\<^bsub>e\<^esub> 
  ((\<phi> \<lparr> cont := Code stmts , 
        vars := ((vars \<phi>)(x := this_field_lookup \<phi> \<chi> y)) \<rparr> ) # \<psi>, \<chi>)" | 

exec_field_assign:
 "cont \<phi> = Code (Seq (AssignToField y x) stmts) \<Longrightarrow> 
  ident_lookup \<phi> x = Some v \<Longrightarrow>
  this_field_update \<phi> \<chi> y v = Some \<chi>' \<Longrightarrow>
  M, (\<phi> # \<psi>, \<chi>) \<rightarrow>\<^bsub>e\<^esub> (\<phi> \<lparr>cont := Code stmts \<rparr> # \<psi>, \<chi>')" |

exec_new: 
 "cont \<phi> = Code (Seq (NewObject x C params) stmts) \<Longrightarrow>
  paramValues = map (ident_lookup \<phi>) params \<Longrightarrow>
  None \<notin> set paramValues \<Longrightarrow>
  M C = Some c \<Longrightarrow>
  length params = length (Class.objFields c) \<Longrightarrow>
  obj' = build_new_object C c (map the paramValues) \<Longrightarrow>
  \<alpha> = fresh_nat (dom \<chi>) \<Longrightarrow>
  \<chi>' = \<chi>(\<alpha> := Some obj') \<Longrightarrow>
  M, (\<phi> # \<psi>, \<chi>) \<rightarrow>\<^bsub>e\<^esub> (\<phi> \<lparr>cont := Code stmts, 
        vars := ((vars \<phi>)(x := Some (VAddr \<alpha>)))\<rparr> # \<psi>, \<chi>')" |

exec_return:  
 "cont \<phi> = Code (SingleStmt (Return x)) \<or> 
  cont \<phi> = Code (Seq (Return x) stmts) \<Longrightarrow>
  cont \<phi>' = NestedCall x' stmts' \<Longrightarrow> 
  M, (\<phi> # \<phi>' # \<psi>, \<chi>) \<rightarrow>\<^bsub>e\<^esub> ((\<phi>' \<lparr> cont := Code stmts', 
        vars := ((vars \<phi>) (x' := ident_lookup \<phi> x))\<rparr>) # \<psi>, \<chi> )"

(*execution for  \<rightarrow>*\<^bsub>e\<^esub>  *)
text \<open>We formally define the execution of more steps @{term exec_rtrancl}, 
which is the reflexive, transitive closure of @{term exec}, as follows. \<close>

inductive 
exec_rtrancl:: "Module \<Rightarrow> Config \<Rightarrow> Config \<Rightarrow> bool" ("_, _ \<rightarrow>\<^bsub>e\<^esub>\<^bsup>*\<^esup>  _") 
  where
exec_rtrancl_equiv: "\<sigma> = \<sigma>' \<Longrightarrow> M, \<sigma> \<rightarrow>\<^bsub>e\<^esub>\<^bsup>*\<^esup> \<sigma>'" | 
exec_rtrancl_trans: "\<lbrakk> M, \<sigma> \<rightarrow>\<^bsub>e\<^esub>\<^bsup>*\<^esup> \<sigma>''; M, \<sigma>'' \<rightarrow>\<^bsub>e\<^esub> \<sigma>'\<rbrakk> \<Longrightarrow> M, \<sigma> \<rightarrow>\<^bsub>e\<^esub>\<^bsup>*\<^esup> \<sigma>'"

text \<open>To have connections with Chainmail, 
we introduce the concrete syntax @{text "(_, _ \<rightarrow>\<^bsub>e\<^esub> _)"} for @{text "exec"} 
and @{text "(_, _ \<rightarrow>\<^bsub>e\<^esub>\<^bsup>*\<^esup>  _)"} for @{text "exec_rtrancl"}. \<close>

section \<open>Module Linking \label{module_linking}\<close>
text\<open>In @{text"an open world"}, to reason about the operation of a module, 
we need to talk about how it behaves when operating in the presence of other
(possibly untrusted) code. For that purpose, we define what it means 
to combine two modules in a module linking operator. 
Later, this will be used to model the operation of module @{term M} in the
presence of other untrusted modules @{term M'} that it is linked to. \<close>

text \<open>We know that the linking should be well-formed. 
So, the function @{term link_wf} represents the well-formedness of the linking, 
saying that when the two modules do not both define the same class (i.e., when their domains are disjoint). \<close>
definition 
link_wf :: "Module \<Rightarrow> Module \<Rightarrow> bool"
  where
"link_wf M M' \<equiv> dom M \<inter> dom M' = {}"

definition 
moduleAux :: "Module \<Rightarrow> Module \<Rightarrow> ClassName \<Rightarrow> Class option" (infixl "\<circ>\<^bsub>aux\<^esub>" 55)
  where
"(M \<circ>\<^bsub>aux\<^esub>  M')  \<equiv> \<lambda>C. (if C \<in> dom M then M C else M' C)"

text\<open>The next step is to define a module linking operator. 
We introduce concrete syntax @{text "\<circ>\<^bsub>l\<^esub>"} for the module linking operator @{term moduleLinking}.
The function @{term moduleLinking} takes two modules @{term M} and @{term M'} and returns the union of the two. \<close>

definition 
moduleLinking :: "Module \<Rightarrow> Module  \<Rightarrow> Module" (infix "\<circ>\<^bsub>l\<^esub>" 55)
  where
"M \<circ>\<^bsub>l\<^esub> M' \<equiv> (M \<circ>\<^bsub>aux\<^esub>  M')"

text \<open>When the linking is well-formed, it should be commutative and associative. 
We prove that linking is commutative (@{term link_commute}) and associative (@{term link_assoc}) when well-formed.\<close>

lemma link_commute [simp]: "link_wf M M' \<Longrightarrow>  M \<circ>\<^bsub>l\<^esub> M' = M' \<circ>\<^bsub>l\<^esub> M"
  unfolding moduleLinking_def moduleAux_def dom_def
  apply (simp cong: if_cong)+
  apply (auto simp: link_wf_def)
  by fastforce

lemma link_assoc [simp]:
  "link_wf M M' \<Longrightarrow> (M \<circ>\<^bsub>l\<^esub> M') \<circ>\<^bsub>l\<^esub> M'' = M \<circ>\<^bsub>l\<^esub> (M'\<circ>\<^bsub>l\<^esub> M'')"
  unfolding moduleLinking_def moduleAux_def dom_def link_wf_def
  apply (simp cong: if_cong)+
  by auto
  
section \<open>Module pairs and visible-states semantics \label{visible_semantics}\<close>
text\<open> Holistic specifications are useful to talk about the interactions between
a module M and other potentially untrustworthy modules @{term M'} that it might interact with. 
We formally capture these interactions via @{text"visible-state semantics"} 
in which the visible states are those as seen from outside the module @{term M}, 
i.e., those in which some @{term M'} object is running.
We name the module @{term M} and @{term M'} for the internal module and external module, respectively.\<close>

text \<open>This section introduces the formalization of module pairs and visible-states semantics. 
   A visible execution is a sequence of execution steps that looks like this:
  @{text "\<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>\<^sub>2 \<rightarrow>\<^bsub>e\<^esub> ... \<sigma>\<^bsub>n-1\<^esub> \<rightarrow>\<^bsub>e\<^esub> \<sigma>\<^sub>n"} where the class of the @{text "this"} object in
  @{term \<sigma>} comes from the external module @{term M'} and the class of the
  @{text "this"} object in @{term "\<sigma>\<^sub>n"} also comes from the external module @{term M'}. 
  However, the class of the @{text "this"} object in every other @{term "\<sigma>\<^sub>2"}, ..., @{text "\<sigma>\<^bsub>(n-1)\<^esub>"} 
  comes from the internal module @{term M}. 

  We capture this using two inductive definitions. 
  The first one, defined as @{term internal_exec}, talks about the first @{term "n-(2::nat)"} steps of execution, 
  each such step leads to a configuration @{term "\<sigma>\<^sub>i"}, 
  where @{text "2 \<le> i < n"} in which the @{term "this"} object of @{term \<sigma>\<^sub>i} is in the internal module @{term M}.\<close>
inductive 
internal_exec :: 
  "Module \<Rightarrow> Module \<Rightarrow> Config \<Rightarrow> (Config list) \<Rightarrow> Config \<Rightarrow> bool" 
  ("_;_,_ \<rightarrow>\<^bsub>e\<^esub>i\<langle>_\<rangle> _") for M :: Module and M' :: Module 
  where
internal_exec_first_step:
 "link_wf M M' \<Longrightarrow>
  (M \<circ>\<^bsub>l\<^esub> M'), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>' \<Longrightarrow>
  this_class_lookup \<sigma> = Some c \<Longrightarrow> c \<in> dom M' \<Longrightarrow>
  this_class_lookup \<sigma>' = Some c' \<Longrightarrow> c' \<in> dom M \<Longrightarrow>
  internal_exec M M' \<sigma> [\<sigma>'] \<sigma>'" |
internal_exec_more_steps:
 "internal_exec M M' \<sigma> tr \<sigma>' \<Longrightarrow>
  (M \<circ>\<^bsub>l\<^esub> M'), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>'' \<Longrightarrow>
  this_class_lookup \<sigma>'' = Some c \<Longrightarrow> c \<in> dom M  \<Longrightarrow>
  internal_exec M M' \<sigma> (tr@[\<sigma>'']) \<sigma>''"

text \<open>The second inductive definition as @{term visible_exec} 
is just for the final step from @{text "\<sigma>\<^bsub>(n-1)\<^esub>"} to @{term \<sigma>\<^sub>n }.\<close>

inductive 
visible_exec :: "Module \<Rightarrow> Module \<Rightarrow> Config \<Rightarrow> Config \<Rightarrow> bool" ("_;_,_ \<rightarrow>\<^bsub>e\<^esub> _") 
  where
visible_exec_intro: 
 "internal_exec M M' \<sigma> tr \<sigma>' \<Longrightarrow>
  (M \<circ>\<^bsub>l\<^esub> M'), \<sigma>' \<rightarrow>\<^bsub>e\<^esub> \<sigma>'' \<Longrightarrow>
  this_class_lookup \<sigma>'' = Some c \<Longrightarrow> 
  c \<in> dom M'  \<Longrightarrow>
  visible_exec M M' \<sigma> \<sigma>''"

subsection\<open>Determinism\label{deterministic}\<close>
text \<open>There is a critical thing that we need to prove in the execution of the language, 
and the execution of the visible-state semantics is deterministic. 
The language is deterministic when any two executions start from the same state step to the same next state.  
Formally, the execution of the language or the visible-states is deterministic 
if for the same initial state @{term \<sigma>}, there is at most one next state that is reached after one step of execution, i.e., 
if @{term "\<sigma>"} steps to @{term "\<sigma>'"} and also to @{term "\<sigma>''"}, then @{term "\<sigma>' = \<sigma>''"}.
The lemma @{term exec_det} shows that the execution of the language is deterministic. 
The lemma @{term visible_exec_det} also shows that the execution of the visible-state semantics is deterministic. 
To prove this lemma, we need several technical definitions and sub-lemmas such as @{term internal_exec_rev'}, 
@{term internal_exec_is_internal}, or @{term internal_exec_appD} (See Appendix \ref{Deterministic_appendix}).\<close>

text \<open>
To prove the determinism of visible-states semantics, we first need to prove that 
the @{term internal_exec} definition is deterministic. 
To do that, it helps to have an equivalent definition of it that operates in reverse. 
That definition we call @{term internal_exec_rev}, which is defined
as follows via the intermediate definition @{term internal_exec_rev'}.\<close>

inductive 
internal_exec_rev' :: 
 "Module \<Rightarrow> Module \<Rightarrow> Config \<Rightarrow> (Config list) \<Rightarrow> Config \<Rightarrow> bool" 
  ("_;_,_ \<rightarrow>\<^bsub>e\<^esub>ir1\<langle>_\<rangle> _") for M :: Module and M' :: Module 
  where
internal_refl: 
 "internal_exec_rev' M M' \<sigma> [] \<sigma>" |
internal_step: 
 "(M \<circ>\<^bsub>l\<^esub> M'), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>' \<Longrightarrow> 
  this_class_lookup \<sigma> = Some c \<Longrightarrow> c \<in> dom M \<Longrightarrow>
  this_class_lookup \<sigma>' = Some c' \<Longrightarrow> c' \<in> dom M \<Longrightarrow> 
  internal_exec_rev' M M' \<sigma>' tr \<sigma>'' \<Longrightarrow>
  internal_exec_rev' M M' \<sigma> (\<sigma>'#tr) \<sigma>''"

inductive 
internal_exec_rev :: 
  "Module \<Rightarrow> Module \<Rightarrow> Config \<Rightarrow> (Config list) \<Rightarrow> Config \<Rightarrow> bool" 
  ("_;_,_ \<rightarrow>\<^bsub>e\<^esub>ir\<langle>_\<rangle> _") for M :: Module and M' :: Module 
  where
internal_exec_rev_first_step:
 "link_wf M M' \<Longrightarrow>
  (M \<circ>\<^bsub>l\<^esub> M'), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>' \<Longrightarrow>
  this_class_lookup \<sigma> = Some c \<Longrightarrow> c \<in> dom M' \<Longrightarrow>
  this_class_lookup \<sigma>' = Some c' \<Longrightarrow> c' \<in> dom M \<Longrightarrow>
  internal_exec_rev' M M' \<sigma>' tr \<sigma>'' \<Longrightarrow>
  internal_exec_rev M M' \<sigma> (\<sigma>'#tr) \<sigma>''" 
end