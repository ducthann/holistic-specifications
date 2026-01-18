theory Adaptation 
  imports LinkingPreserve_Aux LinkingPreserve
begin 
subsection\<open>Adaptation on runtime configurations\label{adaptation_isabelle}\<close>
text\<open>This section is the most challenging part of giving a formalization. 
Thus, to define whether a runtime configuration satisfies a time assertion, 
we need to adapt a runtime configuration to another to deal with time. \<close>
(*answer the questions of examiner 2 *)
text \<open>To cope with the time concept, we encounter some challenges:  
(a) the validity of assertions in the future must be evaluated in the future configuration 
but utilizing the current configuration's bindings.
For example, the assertion @{text "Will(x.f = 1)"} is satisfied if the field @{term f} 
of the object pointed at by @{term x} in the current configuration has the value 1 
in some future configuration. 
Note that @{term x} may be pointing to a different object in the future configuration 
or may no longer be in scope. 
Therefore, the operator @{text "\<triangleleft>"} is used to combine runtime configurations. 
In particular, @{text "\<sigma> \<triangleleft> \<sigma>'"} adapts the following configuration to the view 
of top frame view of the former, returning a new one whose stack has the top frame 
as received from @{term \<sigma>} and where the @{term cont} has been renamed consistently, 
while the heap is taken from  @{term \<sigma>'}. 
It permits to interpret expressions in the newer configuration @{term \<sigma>'}
but with the variables tied in keeping with the top frame from @{term \<sigma>}.

The second obstacle we need to grab is that 
(b) the current configuration requires to store the code executed 
to determine future configurations. 
We cope with it by storing the residual code in the continuation in each frame.  

Next, (c) we do not desire to observe configurations beyond the frame at the top of the stack. 
We handle it by only getting the top of the frame as pondering future executions. \<close>

text\<open>We give a formalized definition of adaptation on runtime configuration as @{term adaptation}.
In the definition, we need support from @{term "adapt_frame \<sigma> \<sigma>'"}, returning a new frame that consists of
 
(1) A new continuation: it is the same as the continuation of the configuration @{term \<sigma>'}.  
However, we replace all variables @{term "zs"} with fresh names @{term "zs'"} using 
@{term "cont_subst_list (cont \<phi>') zs zs'"}.
The set @{term "zs'"} comes from @{term "fresh_idents (dom (vars \<phi>)) zs"}, which is a 
function generating a list of fresh identifiers where none of the new identifiers 
appear in @{term "dom (vars \<phi>)"} or @{term zs}.

(2) A combination of the variable map from the configuration @{term \<sigma>} with the variable map 
from the configuration @{term \<sigma>'} through the renaming @{term "map_upds (vars \<phi>) zs' (map (\<lambda>z. the ((vars \<phi>') z)) zs)"}.\<close>

text\<open>We present all additional definitions and lemmas to formalize adaptation on 
runtime configurations in  Appendix \ref{Adaptation_appendix}.\<close>

text \<open>The function @{term cont_subst_list} replaces all variables @{term "zs"} with fresh names @{term "zs'"}. \<close>
fun 
cont_subst_list :: 
"Continuation \<Rightarrow> Identifier list \<Rightarrow> Identifier list \<Rightarrow> Continuation" 
  where
"cont_subst_list (Code stmts) zs zs' = 
      (Code (stmts_subst_list stmts zs zs'))" |
"cont_subst_list (NestedCall x stmts) zs zs' = 
      (NestedCall (ident_subst_list x zs zs') (stmts_subst_list stmts zs zs'))"

definition 
adapt_frame :: "Frame \<Rightarrow> Frame \<Rightarrow> Frame"
  where
"adapt_frame \<phi> \<phi>' \<equiv> 
  (let zs = sorted_list_of_set (dom (vars \<phi>'));
       zs' = fresh_idents (dom (vars \<phi>)) zs;
       contn'' = cont_subst_list (cont \<phi>') zs zs' ;
       vars'' = map_upds (vars \<phi>) zs' (map (\<lambda>z. the ((vars \<phi>') z)) zs) in 
       \<lparr>cont = contn'', vars = vars'', this = (this \<phi>')\<rparr>)"
(*term "map_upds (vars \<phi>) zs' (map (\<lambda>z. the ((vars \<phi>') z)) zs)"
term "(cont_subst_list (cont \<phi>') zs zs')"*)
text\<open>The operator $\triangleleft$ denotes adaptation between two runtime configurations, 
defined in function @{term adaptation} below. \<close>
definition 
adaptation :: "Config \<Rightarrow> Config \<Rightarrow> Config option" (" _ \<triangleleft> _") 
  where 
"\<sigma> \<triangleleft> \<sigma>' \<equiv> (case \<sigma> of (\<phi>#_,_) \<Rightarrow>
             (case \<sigma>' of (\<phi>'#\<psi>',\<chi>') \<Rightarrow> 
               let \<phi>'' = adapt_frame \<phi> \<phi>' in 
                Some (\<phi>''#\<psi>',\<chi>') | _ \<Rightarrow> None) 
                      | _ \<Rightarrow> None)" 

subsection\<open>Time\<close>
text\<open>With full support from the definition of Adaptation @{term adaptation}, 
we define \textit{Next} assertion @{term Next} and \textit{Will} assertion @{term Will}.\<close>
text\<open>The function @{term next_visible}, a partial function, is used to reach the next state of visible-state semantics if it exists.\<close>

definition 
next_visible :: "Module \<Rightarrow> Module \<Rightarrow> Config \<Rightarrow> Config option"
  where
"next_visible M M' \<sigma> \<equiv> 
        if (\<exists>\<sigma>'. (M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>')) 
        then Some (THE \<sigma>'. (M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub> \<sigma>')) 
        else None"

text \<open>Similarly, the function @{term "will_visible"} is used to reach the future state of visible-state semantics 
when it existed.\<close>
definition 
will_visible :: "Module \<Rightarrow> Module \<Rightarrow> Config \<Rightarrow> Config option"
  where
"will_visible M M' \<sigma> \<equiv> 
        if (\<exists>\<sigma>'. (M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub>\<^bsup>*\<^esup> \<sigma>')) 
        then Some (THE \<sigma>'. (M;M', \<sigma> \<rightarrow>\<^bsub>e\<^esub>\<^bsup>*\<^esup> \<sigma>')) 
        else None"

text\<open>The assertion @{term "Next A"} holds if @{term A} holds in some configuration @{term \<sigma>'} which arises from execution @{term \<phi>}, 
where @{term \<phi>} is the top frame of @{term \<sigma>}. By requiring that @{term "next_visible M M' ([\<phi>],\<chi>)"} rather than 
@{term "next_visible M M' \<sigma>"}, we are restricting the set of possible next configurations to those caused by the top frame.\<close>

definition 
Next :: "Assertion \<Rightarrow> Assertion" 
  where 
"Next A \<equiv> 
   \<lambda>M M' \<sigma>. (case \<sigma> of (\<phi>#_,\<chi>) \<Rightarrow> 
              (case (next_visible M M' ([\<phi>],\<chi>)) of Some \<sigma>' \<Rightarrow> 
                  (case (([\<phi>],\<chi>) \<triangleleft>  \<sigma>') of 
                     Some adpt \<Rightarrow> (A M M' adpt)| 
                  None \<Rightarrow> None) | 
               None \<Rightarrow> None)  |
             _  \<Rightarrow> None)"

text \<open>Similar to the assertion @{term "Next A"}, we define the assertion @{term "Will A"}.
It says that the assertion holds when @{term A} holds in some configuration @{term \<sigma>'} 
which arises from execution @{term \<phi>}, where @{term \<phi>} is the top frame of @{term \<sigma>}.
However, it considers in more future steps instead of in the successive step.\<close>
definition 
Will :: "Assertion \<Rightarrow> Assertion" 
  where 
"Will A \<equiv> 
   \<lambda>M M' \<sigma>. (case \<sigma> of (\<phi>#_,\<chi>) \<Rightarrow> 
              (case (will_visible M M'([\<phi>],\<chi>) ) of Some \<sigma>' \<Rightarrow> 
                  (case (([\<phi>],\<chi>) \<triangleleft>  \<sigma>') of 
                     Some adpt \<Rightarrow> (A M M' adpt)| 
                  None \<Rightarrow> None) | 
               None \<Rightarrow> None)  |
             _  \<Rightarrow> None)"

subsection\<open>Authority\<close>
text \<open>Authority (\textit{Changes}) assertion @{term Changes} is defined to give conditions for change to occur.
The partial function @{term Changes} on expression @{term e} is used to assert  
the evaluation of expression @{term e} in the next configuration @{term \<sigma>'} distinguishes from 
one in the current configuration @{term \<sigma>}.\<close> 

text \<open>In particular, the @{term "Changes e"} says that there exists an expression @{term v} such that the value of 
the expression @{term v} and @{term e} is the same.
However, the expression @{term v} and @{term e}'s values are no longer the same in the next configuration.\<close>
definition 
Changes :: "Expr \<Rightarrow> Assertion"
  where 
"Changes e \<equiv>  \<lambda>M M' \<sigma>.  
              (case (next_visible M M' \<sigma>) of Some \<sigma>' \<Rightarrow> 
                  (case (\<sigma> \<triangleleft> \<sigma>') of Some adpt \<Rightarrow> 
                      (case expr_eval e \<sigma> of Some v1 \<Rightarrow> 
                            (case expr_eval e adpt of Some v2 \<Rightarrow> 
                                     Some (v1 \<noteq> v2) |
                                                        None \<Rightarrow> None ) | 
                                                None \<Rightarrow> None) | 
                                          None \<Rightarrow> None) | 
                                                None \<Rightarrow> None)"

subsection\<open>Modules Satisfying Assertions\<close>
text\<open>
The section exhibits how we formally define whether a module satisfies an assertion @{term Module_sat}.
Here, @{term "Module_sat M A"} holds when for all external modules @{term M'} and all @{text "Arising"} runtime configuration @{term \<sigma>},
the assertion @{term A} is satisfied. Note that all runtime configuration @{term \<sigma>} is observed as @{term Arising} configurations. \<close>
(* TODO: work out what this should say when the assertion is not well defined, i.e. when there is some \<sigma> in Arising for which the assertion evaluates to None *)
definition 
Module_sat :: "Module \<Rightarrow> Assertion \<Rightarrow> bool" 
  where
"Module_sat M A \<equiv> (\<forall> M' \<sigma>. (\<sigma> \<in> Arising M M') \<longrightarrow> 
                  (A M M' \<sigma> = None \<or> A M M' \<sigma> = Some True))"
end