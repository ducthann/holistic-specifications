theory LinkingPreserve
  imports LinkingPreserve_Aux
begin 
text \<open>Then, we put the lemma @{term link_exec} 
to show that the module linking preserves one-module if its module linking is defined.\<close>
lemma link_exec: 
  "\<lbrakk> M, \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'; link_wf M M' \<rbrakk> \<Longrightarrow> (M \<circ>\<^bsub>l\<^esub> M'), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'"
  by (simp add: link_exec_aux)

text \<open>Moreover, the module linking preserves visible state semantics also, as shown in lemmas 
@{term visible_exec_linking_1} and @{term visible_exec_linking_2}.
Since the definition of visible-state semantics @{term visible_exec}, 
is based on the definitions of internal execution\\ @{term internal_exec}, 
we need to prove that the internal execution is also preserved by linking as shown in 
lemmas @{term internal_linking_1} and @{term internal_linking_2} as well. \\
Proofs of lemma @{term internal_linking_1} and @{term internal_linking_2} 
are by structural induction on the definition of @{term internal_exec}.\<close>

text \<open>The lemma @{text "internal_linking_1"} guarantees that 
@{text "M; M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>'"} implies that all intermediate configurations 
are external to @{term M'} and thus also to @{term "M' \<circ>\<^bsub>l\<^esub> M''"}.  \<close> 
lemma internal_linking_1:
  "\<lbrakk>M; M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>'; link_wf_3M M M' M''\<rbrakk> \<Longrightarrow> 
         M;(M' \<circ>\<^bsub>l\<^esub> M''), \<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>'" 
  by (simp add: internal_linking_1_aux)

text \<open>Similarly, the lemma @{text "internal_linking_2"} guarantees that 
@{text "M; M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>'"} implies that all intermediate configurations 
are internal to @{term M} and thus also to @{term "M \<circ>\<^bsub>l\<^esub> M''"}. \<close> 
lemma internal_linking_2: 
  "\<lbrakk> M; M',\<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>' ; link_wf_3M M M' M''\<rbrakk> \<Longrightarrow> 
   (M \<circ>\<^bsub>l\<^esub> M''); M', \<sigma> \<rightarrow>\<^bsub>e\<^esub>i\<langle>tr\<rangle> \<sigma>'"
  by (simp add: internal_linking_2_aux)

text \<open>Thanks to two useful lemmas @{text "internal_linking_1"} and @{text "internal_linking_1"}, 
we also gain the guarantee of module linking preserves visible state semantics. 
Proofs of lemmas @{term visible_exec_linking_1} and @{term visible_exec_linking_2} 
are by structural induction on the definition of @{term visible_exec}.\<close>

lemma visible_exec_linking_1:
  "\<lbrakk>(M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'); (link_wf_3M M M' M'')\<rbrakk> \<Longrightarrow> 
    M; (M' \<circ>\<^bsub>l\<^esub> M''), \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'"
  by (simp add: visible_exec_linking_1_aux) 

lemma visible_exec_linking_2:
  "\<lbrakk>(M;M',\<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'); (link_wf_3M M M' M'')\<rbrakk> \<Longrightarrow> 
    (M \<circ>\<^bsub>l\<^esub> M''); M', \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>'"
  by (simp add: visible_exec_linking_2_aux) 

text\<open>We make the proof details of Linking modules preserving execution 
in Appendix \ref{LinkingPreserve_appendix}.\<close>

section \<open>Initial and Arising configurations \label{initArising}\<close>
text\<open>What does it mean for a holistic specification to hold for 
a module M when linked against some external module @{term M'}? 
It means that the property holds for all @{term Arising} configurations of @{term M} with @{term M'}. 
These are the configurations that can be reached in the visible state semantics
of @{term M} with @{term M'} when execution begins from the initial, empty configuration. 
We formally define these ideas below.\<close>

text \<open> Now, we assume that the initial stack frame maps no local variables.
  Note that we let the continuation be arbitrary. \<close>
definition 
initial_frame :: "Frame \<Rightarrow> bool" 
  where
"initial_frame \<phi> \<equiv> (vars \<phi> = Map.empty \<and> this \<phi> = Null)"

text \<open>Suppose we have defined the execution of more steps @{term exec_rtrancl},
which is the reflexive, transitive closure of @{term exec}. In that case,  
we also want to define the execution of more steps @{term exec_module}, 
saying that it is the reflexive, transitive closure of visible execution @{term exec}. 
We formally define the execution @{term exec_module} as follows.\<close>

inductive 
exec_module :: 
  "Module \<Rightarrow> Module \<Rightarrow> Config \<Rightarrow> Config \<Rightarrow> bool" ("_;_, _ \<rightarrow>\<^bsub>e\<^esub>\<^bsup>*\<^esup> _") 
  where
exec_module_equiv: "\<sigma> = \<sigma>' \<Longrightarrow> M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub>\<^bsup>*\<^esup> \<sigma>'" | 
exec_module_trans: "\<lbrakk>(M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub>\<^bsup>*\<^esup> \<sigma>''); (M; M', \<sigma>'' \<rightarrow>\<^bsub>e\<^esub> \<sigma>')\<rbrakk> \<Longrightarrow> 
                     M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub>\<^bsup>*\<^esup> \<sigma>'"

text \<open>Initial configurations @{term Initial} might contain arbitrary code but no objects.\<close>
definition 
Initial :: "(Stack \<times> Heap) \<Rightarrow> bool" 
  where
"Initial \<sigma> \<equiv> (case \<sigma> of (\<psi>,\<chi>) \<Rightarrow> 
                  (case \<psi> of ([\<phi>]) \<Rightarrow> 
                    initial_frame \<phi> \<and> \<chi> = Map.empty 
                | _ \<Rightarrow> False))"

text \<open>From initial configurations @{term Initial}, execution of code from module-pair @{text "(M; M')"},
  creates a set of Arising configurations @{term Arising}.\<close>
definition 
Arising :: "Module \<Rightarrow> Module \<Rightarrow> Config set " 
  where
"Arising M M' \<equiv> {\<sigma>.\<exists>\<sigma>\<^sub>0. (Initial \<sigma>\<^sub>0 \<and> (M;M', \<sigma>\<^sub>0 \<rightarrow>\<^bsub>e\<^esub>\<^bsup>*\<^esup> \<sigma>))}"

text\<open>Notice that @{term "M;M', \<sigma>\<^sub>0 \<rightarrow>\<^bsub>e\<^esub>\<^bsup>*\<^esup> \<sigma>"} is @{text"visible-state semantics"} 
introduced in Section \ref{visible_semantics}.\<close>

section \<open>Assertions - Classical Assertions \label{classicAssertion}\<close>
text\<open>
We have defined the object-based programming language and
its semantics, including the visible state semantics, and proved
them deterministic. However, we have not yet defined the language
in which holistic specifications are expressed. We now do that 
by formally defining the assertions of holistic specifications and 
giving them meaning over the visible state semantics of the 
programming language defined above. 
We give the formalization of syntax and semantics of holistic assertions in this section.\<close>
subsection\<open>Syntax of Assertions and its standard semantics\<close>

text\<open>The validity of assertions @{term Assertion} has a form of @{text "M; M',\<sigma> \<Turnstile> A"} 
where the module @{term M} and @{term M'} are internal and external, respectively. 
The assertion returns a @{typ "bool option"} type rather than a @{typ bool}. 
For instance, if we compare two expressions @{term e} and @{term e'} and one of them
evaluates to @{term None}, then the semantics of the comparison is undefined.
Hence the semantics of assertions is partial, represented using the option type as with other
partial functions.\<close>

text\<open>Unlike the syntax of the programming language, which is deeply embedded, 
we decided to embed assertions in our formalization shallowly. 
It was done to enable us to extend the set of assertions, later on, more efficiently.\<close>

type_synonym Assertion = "Module \<Rightarrow> Module \<Rightarrow> Config \<Rightarrow> bool option" 

text\<open>Assertions consist of pure expressions such as @{term atrue} and @{term afalse}.  \<close>

datatype Expr =  ENull | EId Identifier | EField Expr FieldName

definition 
atrue :: "Assertion"
  where
"atrue  \<equiv> \<lambda>M M' \<sigma>. Some True"

definition 
afalse :: "Assertion"
  where
"afalse  M M' \<sigma> \<equiv> Some False"

text \<open> Expressions support nested field lookups, e.g., @{text "x.f.g"} via @{text "(EField (EField (EId x) f) g)"}.\<close>
(*function to evaluate of variable x *) 
fun 
evalVar :: " Identifier \<Rightarrow> Config \<Rightarrow> Value option"
  where
"evalVar x (\<phi>#\<psi>,\<chi>) =  ident_lookup \<phi> x" |
"evalVar x ([],\<chi>)  =  None"

text\<open> Recall that expressions denote values. We, therefore, define the semantics of expressions 
via the following partial function. Note that expression might not evaluate a value, 
e.g., for a field lookup for a non-existent object, in which case the semantics returns @{term None}. 
Otherwise, it returns @{term "Some v"}, where @{term v} is the value the expression denotes, in configuration @{term \<sigma>}.\<close>

primrec 
expr_eval :: "Expr \<Rightarrow> Config \<Rightarrow> Value option" 
  where
"expr_eval ENull \<sigma> = Some (VAddr Null)" |
"expr_eval (EId x) \<sigma> = evalVar x \<sigma>" |
"expr_eval (EField e f) \<sigma> = 
     (case (expr_eval e \<sigma>) of Some (VAddr a) \<Rightarrow> 
           field_lookup (snd \<sigma>) a f)"

text \<open>We define generic comparisons between expressions. 
For example, the notation of \textit{greater than} would be expressed as @{text "acompare (>) e e'"}. \<close>

definition 
acompare :: "(Value \<Rightarrow> Value \<Rightarrow> bool) \<Rightarrow> Expr \<Rightarrow> Expr \<Rightarrow> Assertion"
  where
"acompare c e e' \<equiv> \<lambda>M M' \<sigma>. 
    (case (expr_eval e \<sigma>) of Some v \<Rightarrow>
        (case (expr_eval e' \<sigma>) of Some v' \<Rightarrow> Some (c v v')     
                                | None \<Rightarrow> None)
                           | None \<Rightarrow> None)"

text\<open>We give formalized definitions of the semantics of assertions involving expressions.
The partial function @{term "expr_class_lookup"} is used to look up the class where expression @{term e} is located in
the runtime configuration @{term \<sigma>}.\<close>

fun 
expr_class_lookup :: "Config \<Rightarrow> Expr \<Rightarrow> ClassName option"
  where
"expr_class_lookup \<sigma> e =  
   (case \<sigma> of (\<phi>#\<psi>,\<chi>) \<Rightarrow>
       (case (expr_eval e \<sigma>) of Some (VAddr a) \<Rightarrow>
            (case \<chi> a of Some obj \<Rightarrow> Some (className obj) |  None \<Rightarrow> None ))
            | _ \<Rightarrow> None)"

text\<open>The assertion @{term aExpClassId} states whether an expression @{term e} belongs to a class identifier @{term ClassId}.\<close>
(*text \<open> Basic assertion M; M', \<sigma> \<Turnstile> e : ClassId \<close> *)
definition 
aExpClassId :: "Expr \<Rightarrow> ClassName \<Rightarrow> Assertion"
  where
"aExpClassId e ClassId \<equiv> 
     \<lambda>M M' \<sigma>. (case (expr_class_lookup \<sigma> e) of None \<Rightarrow> None
                                         | Some cid \<Rightarrow> Some (cid = ClassId))"

text\<open>The function @{term expInS} checks the address of the expression @{term e}
is in the set of addresses of the given set @{term S}.\<close>
(* the function checks [e]\<sigma> \<in> [S]\<sigma> or not *)
fun 
expInS :: "Config \<Rightarrow> Expr \<Rightarrow> Identifier \<Rightarrow> bool option"
  where
"expInS \<sigma> e S =  
   (case (expr_eval e \<sigma>) of Some (VAddr a) \<Rightarrow>
                 (case (evalVar S \<sigma>) of Some v \<Rightarrow> 
                        (case v of VAddr addr \<Rightarrow> None |
                             VAddrSet addrSet \<Rightarrow> (Some (a \<in> addrSet))) |  
                  None \<Rightarrow> None) | 
            None \<Rightarrow> None)"
(* assertion  M; M', \<sigma> \<Turnstile> e \<in> S with e is an experssion and S is a set  *)
text\<open> The assertion @{term aExpInS} presents whether an expression @{term e} belongs to a given set @{term S}.\<close>

definition 
aExpInS :: "Expr \<Rightarrow> Identifier \<Rightarrow> Assertion" 
  where 
"aExpInS e S  \<equiv> \<lambda> M M' \<sigma>. (expInS \<sigma> e S)"

text\<open> We formalize the meaning of standard logical connectives between assertions.
For example, the logical conjunction of two assertions @{term A} and @{term A'} 
is expressed as @{term "aAnd A A'"}. 
Similarly, the logical disjunction, negation, and implication are expressed as 
@{term "aOr A A'"}, @{term "aNot A"}, and @{term "aImp A A'"}, respectively. \<close> 

text \<open> To support such assertions, we define a generic binary operator between assertions. 
For example, the notation of \textit{implication} would be expressed as @{text "bopt (\<longrightarrow>) (A M M' \<sigma>) (A' M M' \<sigma>)"}.\<close>

definition 
bopt :: 
"(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> bool option \<Rightarrow> bool option \<Rightarrow> bool option" 
  where
"bopt f a b \<equiv> 
   (case a of Some a' \<Rightarrow> 
       (case b of Some b' \<Rightarrow> Some (f a' b')
                   | None \<Rightarrow> None)
               | None \<Rightarrow> None)"

definition 
aImp :: "Assertion \<Rightarrow> Assertion \<Rightarrow> Assertion"
  where 
"aImp A A' \<equiv> \<lambda>M M' \<sigma>. bopt (\<longrightarrow>) (A M M' \<sigma>) (A' M M' \<sigma>)"

definition 
aAnd:: "Assertion \<Rightarrow> Assertion \<Rightarrow> Assertion"
  where 
"aAnd A A' \<equiv> \<lambda>M M' \<sigma>. bopt (\<and>) (A M M' \<sigma>) (A' M M' \<sigma>)"

definition 
aOr:: "Assertion \<Rightarrow> Assertion \<Rightarrow> Assertion"
  where 
"aOr A A' \<equiv> \<lambda>M M' \<sigma>. bopt (\<or>) (A M M' \<sigma>) (A' M M' \<sigma>)"

definition 
aNot:: "Assertion  \<Rightarrow> Assertion"
  where 
"aNot A  \<equiv>\<lambda>M M' \<sigma>. case (A M M' \<sigma>) of None \<Rightarrow> None | Some a' \<Rightarrow> Some (\<not> a')"

text\<open>We also give the universal and existential quantification for holistic assertions.
The universal quantification is expressed formally as @{term "aAll fA"}, 
and the existential quantification is presented as @{term "aEx fA"}.
We represent an assertion like @{term "\<forall>x. P x"}, by having P be a function that takes
the identifier @{term x} as an argument and returns an assertion. 
It is an instance of Higher-Order Abstract Syntax.  \<close>

definition 
aAll :: "(Identifier \<Rightarrow> Assertion) \<Rightarrow> Assertion"
  where
"aAll fA \<equiv> \<lambda>M M' \<sigma>. (if (\<exists>v'. fA v' M M' \<sigma> = None) 
                     then None
                     else Some (\<forall>v. the (fA v M M' \<sigma>)))" 
(*text \<open> (\<forall>x. x = x) is equivalent to true, when it is defined *) 
text \<open>It is similar to an assertion like @{term "\<exists>x. P x"}. \<close>
definition 
aEx :: "(Identifier \<Rightarrow> Assertion) \<Rightarrow> Assertion"
  where
"aEx fA \<equiv> \<lambda>M M' \<sigma>. (if (\<exists>v'. fA v' M M' \<sigma> = None) 
                    then None
                    else Some (\<exists>v. the (fA v M M' \<sigma>)))" 

subsection\<open>Properties of classical logic \label{assertclassical}\<close>
text\<open>Here, we deliver formal proofs of properties that apply to conjunction, disjunction, 
negation, implication, universal quantification, as well as existential quantification 
to show that holistic assertions are classical.
Remember that assertions are partial. These properties hold only for well-formed assertions whose
semantics are not undefined. We capture this formally via the definition @{term "Assert_wf"} below.\<close>

definition 
Assert_wf:: "Assertion \<Rightarrow> Module \<Rightarrow> Module \<Rightarrow> Config \<Rightarrow> bool"
  where
"Assert_wf A M M' \<sigma>  \<equiv> A M M' \<sigma> \<noteq> None" 
(*need a name for all lemmas *)
text\<open>We are taking an example to show that 
holistic assertions are distributive property\\ @{term aDistributive_1} 
of logical conjunction over logical disjunction for assertion @{term A}, @{term A'} and @{term A''}.
Other properties can be found in Section \ref{appendixproperties}.\<close>
lemma aDistributive_1:
  "\<lbrakk>Assert_wf A M M' \<sigma>;  Assert_wf A' M M' \<sigma>; Assert_wf A'' M M' \<sigma> \<rbrakk> \<Longrightarrow> 
    (aAnd (aOr A  A') A''  M M' \<sigma>) = (aOr (aAnd A A'') (aAnd A' A'') M M' \<sigma>)"
  unfolding aAnd_def aOr_def bopt_def option.case_eq_if by auto

section \<open>Assertions - Access, Control, Space, Authority, and Viewpoint \label{assertHolistic}\<close>
text\<open>In this section, we focus on the formalization of holistic concepts. 
These consist of permission, control, space, authority, and viewpoint.\<close>

subsection\<open>Access\<close>
text\<open>Access or permission states an object has a direct path to another object. 
In more detail, in the current frame, the access assertions are defined as three cases: 
(1) two objects are aliases, (2) the first points to an object with a field 
whose value is the same as the second object,
(3) the first object is currently executing an object, and the second object is a local parameter 
that appears in the code in the continuation.\<close>

text\<open>In particular, we formalize access assertion @{term Access} 
with supporting functions @{term thisEval} and @{term evalThis}.
The partial function @{term thisEval} is used to look up the address of @{term this} object 
in runtime configuration @{term \<sigma>}. The function returns @{term None} in case of lookup failure.\<close>

fun 
thisEval :: "Config \<Rightarrow> Value option"
  where
"thisEval \<sigma> =  
   (case \<sigma> of (\<phi>#_, _) \<Rightarrow> 
        (case (this \<phi>) of 
                addr \<Rightarrow> Some (VAddr addr))
            | _ \<Rightarrow> None)"

text\<open>The partial function @{term evalThis} is used to look up the field @{term f} from @{term this} object 
in runtime configuration @{term \<sigma>}. The function returns @{term None} in case of lookup failure.\<close>

fun 
evalThis :: "FieldName \<Rightarrow> Config \<Rightarrow> Value option"
  where
"evalThis f \<sigma> = 
    (case \<sigma> of (\<psi>,\<chi>) \<Rightarrow> 
            (case \<psi> of [] \<Rightarrow> None 
                  | (\<phi>#\<psi>) \<Rightarrow> this_field_lookup \<phi> \<chi> f))"
(*define \<sigma>.cont *)
text\<open>The function @{term ConfigCont} obtains the continuation @{term cont} from the configuration @{term \<sigma>}.\<close>   
definition 
ConfigCont :: "Config \<Rightarrow> Continuation"
  where 
"ConfigCont \<sigma> \<equiv> (case \<sigma> of (\<phi>#_, _) \<Rightarrow> cont \<phi>)"

text \<open>
The assertion @{term "Access x y"} holds if in runtime configuration @{term \<sigma>}, 
 
(1) the value of identifier @{term x} and @{term y} is the same, or

(2) there exists a field @{term f} such that the value of the field @{term f} and the identifier @{term y} is the same, or 

(3) the value of identifier @{term x} and the @{term this} object is the same, as well as 
the value of identifier @{term y} and @{term z} is also the same, where @{term z} is a local parameter 
in continuation @{term "cont"}. 
\<close>

definition
Access:: "Identifier \<Rightarrow> Identifier \<Rightarrow> Assertion"
  where
"Access x y \<equiv> \<lambda>M M' \<sigma>. 
                  if (evalVar x \<sigma> = None \<or> evalVar y \<sigma> = None) 
                  then None 
                  else Some ( (evalVar x \<sigma> = evalVar y \<sigma>) \<or> 
                       (\<exists>f. (evalThis f \<sigma> = evalVar y \<sigma>)) \<or> 
                       ((evalVar x \<sigma> = thisEval \<sigma>) \<and> 
                       (\<exists>z z1 stmts. ((Code stmts =  ConfigCont \<sigma>) \<or> 
                       (NestedCall z1 stmts =  ConfigCont \<sigma>)) \<and>  
                       (z \<in>  stmts_idents stmts) \<and>  
                       (evalVar y \<sigma> = evalVar z \<sigma>))))"

subsection\<open>Control\label{control_isabelle}\<close>
text\<open>Control assertion represents the object making a function call on another object. 
We give a formalized definition of @{term Calls}, which goes along with 
supporting functions:\\ @{term idents_list_undef} and @{term idents_list_equal}.\<close>

text\<open>Since the control assertion has a form @{text "x calls y.m(params)"}, 
and the identifier @{term x}, @{term y}, as well as all elements in the list @{term params} should be defined, 
we give an auxiliary function @{term idents_list_undef} to check for any undefined identifiers in the list of identifiers, 
given the configuration @{term \<sigma>}.\<close>

fun 
idents_list_undef:: "Identifier list \<Rightarrow> Config \<Rightarrow> bool"
  where 
"idents_list_undef [] \<sigma> = False" | 
"idents_list_undef (x#xs) \<sigma> = 
              ((evalVar x \<sigma> = None) \<or> (idents_list_undef xs \<sigma>))"
text\<open>Then, the function @{term idents_list_equal} checks that the value of each element of the first and second identifier list are equal 
in runtime configuration @{term \<sigma>}.\<close>

fun 
idents_list_equal:: "Identifier list \<Rightarrow> Identifier list \<Rightarrow> Config \<Rightarrow> bool" 
  where 
"idents_list_equal [] [] \<sigma> = True" | 
"idents_list_equal (z#zs) [] \<sigma> = False" | 
"idents_list_equal [] (v#vs) \<sigma> = False" | 
"idents_list_equal (z#zs) (v#vs) \<sigma> = 
       ((evalVar z \<sigma> = evalVar v \<sigma>) \<and> (idents_list_equal zs vs \<sigma>))"

text \<open>
The assertion @{term "Calls x y m zs"} holds if in runtime configuration @{term \<sigma>},

(1) the identifier @{term x}, @{term y} and all identifiers in list @{term zs} are defined, and 

(2) the address of @{term this} object equals to the value of the caller @{term x}

(3) there are a receiver @{term u} and arguments @{term vs} with the same method @{term m} in runtime configuration @{term \<sigma>} 
such that the value of the identifier @{term y} and @{term u} is the same, and the value of 
each element of the list @{term zs} and @{term vs} is equal. \<close>
definition 
Calls :: 
  "Identifier \<Rightarrow> Identifier \<Rightarrow> MethodName \<Rightarrow> Identifier list \<Rightarrow> Assertion"
  where
"Calls x y m zs \<equiv> \<lambda>M M' \<sigma>. 
           if (evalVar x \<sigma> = None \<or> evalVar y \<sigma> = None \<or> 
              (idents_list_undef zs \<sigma>)) 
           then None 
           else 
                Some (( thisEval \<sigma> = evalVar x \<sigma>) \<and> 
                (\<exists> a u vs stmts.(ConfigCont \<sigma> = 
                Code (Seq (MethodCall a u m vs) stmts)) \<and> 
                (evalVar y \<sigma> = evalVar u \<sigma>) \<and> idents_list_equal zs vs \<sigma>))"

subsection\<open>Viewpoint\<close>
(* A function to return the next visible state, if it exists. *)
text\<open>Viewpoint assertion represents whether an object belongs to the internal or external module. 
The formalization of @{term Internal} and @{term External} can be found as follows.\<close>

text\<open>First, we define a function @{term Ident_class_lookup} to look up the class where identifier @{term x} is located
in runtime configuration @{term \<sigma>}. The function returns @{term None} in case of failure.\<close>

fun 
Ident_class_lookup :: "Config \<Rightarrow> Identifier \<Rightarrow> ClassName option"
  where
"Ident_class_lookup \<sigma> x =  
   (case \<sigma> of (\<phi>#\<psi>,\<chi>) \<Rightarrow>
       (case (evalVar x \<sigma>) of 
                Some (VAddr a) \<Rightarrow> (case \<chi> a of 
                  Some obj \<Rightarrow> Some (className obj) 
                | None \<Rightarrow> None ))
            | _ \<Rightarrow> None)"

text\<open>Then, the assertion @{term "External x"} holds if the object @{term x} is outside the scope of module @{term M} 
in configuration @{term \<sigma>}.\<close>

definition 
External :: "Identifier \<Rightarrow> Assertion" 
  where
"External x \<equiv> \<lambda> M M' \<sigma>. 
              (case (Ident_class_lookup \<sigma> x) of 
                    None   \<Rightarrow> None | 
                    Some c \<Rightarrow> Some (c \<notin> dom M))"

text\<open> Otherwise, the assertion @{term "External x"} asserts that the object @{term x} is in module @{term M} 
in runtime configuration @{term \<sigma>}.\<close>

definition 
Internal :: "Identifier \<Rightarrow> Assertion"
  where
"Internal x \<equiv> \<lambda> M M' \<sigma>. 
              (case (Ident_class_lookup \<sigma> x) of 
                    None \<Rightarrow> None  | 
                  Some c \<Rightarrow> Some (c \<in> dom M))"

subsection\<open>Space \label{SpaceAssetion}\<close>
(* term "expr_eval S \<sigma> = Some (VAddrSet {a,b,c})" *)
text\<open>To define space assertion, we give a function @{term restrictConf} to create a new heap with 
only objects in the given set @{term S} in runtime configuration @{term \<sigma>}. \<close>

definition 
hRst :: "Heap \<Rightarrow> Config \<Rightarrow> Identifier \<Rightarrow> Heap" 
  where 
"hRst \<chi> \<sigma> S  \<equiv> 
     \<lambda>a. (case (evalVar S \<sigma>)  of  
              None \<Rightarrow> None | 
              Some v \<Rightarrow> (case v of VAddr addr \<Rightarrow> None |
                            VAddrSet addrSet \<Rightarrow> if a \<in> addrSet 
                                                then \<chi> a 
                                                else None ))"

text\<open>The function @{term restrictConf} updates the new heap @{term \<chi>'} 
after restricting the given set @{term S} in runtime configuration @{term \<sigma>}.\<close>

definition
restrictConf :: "Identifier \<Rightarrow> Config \<Rightarrow> Config option"
  where
"restrictConf S \<sigma> \<equiv>  
  (case \<sigma> of (\<psi>, \<chi>) \<Rightarrow> (let \<chi>' = (hRst \<chi> \<sigma> S) in 
                          Some (\<psi>, \<chi>')))" 

definition 
transConf :: "(Config \<Rightarrow> Config option) \<Rightarrow> Assertion \<Rightarrow> Assertion" 
  where
"transConf transf A  \<equiv> 
     \<lambda>M M' \<sigma>. (case transf \<sigma> of None \<Rightarrow> None | Some b \<Rightarrow> A M M' b)"

text \<open>Thanks to the restriction operator @{term restrictConf}, 
we obtain the semantics of the space assertion @{term In}.\<close>
definition 
In :: "Identifier \<Rightarrow> Assertion \<Rightarrow> Assertion" 
  where
"In S \<equiv> transConf (restrictConf S)"

(* proof of  (A \<Rightarrow> B) in S  \<equiv> (A in S \<Rightarrow> B in S) *) 
(*text\<open>The @{term Distrib_In} is the formalized proof of Lemma \ref{Distrib_In} in Section \ref{discusspolicies}. \<close>
*)

text\<open> After having the definition of space assertion @{term "In"}, 
we also provide lemmas related to spatial connective assertions.
Lemma @{term "Distrib_In"} proves the distributive property of space assertion over logical implication.\<close>  
lemma Distrib_In: 
  "(aImp (In S A) (In S B) M M' \<sigma>) = 
       (In S(aImp A B)) M M' \<sigma>"
  by (simp add: In_def aImp_def bopt_def option.case_eq_if transConf_def)

text\<open>Also, the lemma @{term not_In} demonstrates the negation property of space assertion.\<close> 
(* proof of \<not> (A in S) \<equiv> (\<not> A) in S *) 
lemma not_In: 
  "aNot (In S A) M M' \<sigma> = (In S (aNot A)) M M' \<sigma>"
proof -
  have "\<forall>f fa p fb fc. aNot (transConf fc fb) fa f p = 
          transConf fc (aNot fb) fa f p \<or> fc p = None"
    using aNot_def transConf_def 
    by force
  thus ?thesis
    using In_def aNot_def transConf_def 
    by fastforce
qed
end