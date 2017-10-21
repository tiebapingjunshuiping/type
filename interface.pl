mywrite(X):-write('\n'),write(X),write('\n').
<:(Self,Self,Env):-!.
<:(Sub,Super,Env):-inherit(Sub,Super,Env),!.
<:(Sub,Super,Env):-inherit(Sub,X,Env),<:(X,Super,Env).

inherit(Sub,Super,Env):-member(extends(Sub,Super),Env).

belong(Obj,Memb,Sym,Obj_env,Memb_env):- <:(Obj,X,Obj_env),has(X,Memb,Sym,Memb_env).

has(Obj,Memb,Sym,Env):-member(mem(Obj,Memb,Sym),Env).
has(Obj,Name,Type,Env):-member(method(Obj,Name,Type,_),Env).

assign_match(Dest,Source,Env):- <:(Source,Dest,Env).

para_match([],[],Env).
para_match([Para|X],[Argu|Y],Env):-assign_match(Argu,Para,Env),para_match(X,Y,Env).

put_extends(extends(Sub,Super),Env_new,Env_old):- <:(Super,Sub,Env_old),!,false.
put_extends(extends(Sub,_),Env_new,Env_old):- (member(extends(Sub,_),Env_old);member(extends(_,Sub),Env_old)),!,false.
put_extends(X,Env_new,Env_old):-Env_new=[X|Env_old].

put_mem(Obj,Memb,Env_new,Env_old):-has(Obj,Memb,_,Env_old),!.
put_mem(Obj,method(Name,Arg,Body),Env_new,Env_old):-findall(arg(X,Y),member(X,Arg),Z),Env_new=[method(Obj,Name,[Ret|Z],Body)|Env_old],!.
put_mem(Obj,Memb,Env_new,Env_old):-Env_new=[mem(Obj,Memb,X)|Env_old].

make_constrait_all(Obj_env,Memb_env,[]).
make_constrait_all(Obj_env,Memb_env,[X|Y]):-
  make_constrait(Obj_env,Memb_env,X),
  make_constrait_all(Obj_env,Memb_env,Y).

make_constrait(Obj_env,Memb_env,method(Obj,Name,[Ret|Arg],Body)):-
  pasre_body(Obj_env,Memb_env,Obj,Ret,[Arg],Body).



pasre_body(_,_,_,Ret,_,[]):-Ret=void,!.
pasre_body(Obj_env,Memb_env,Obj,Ret,Stack,[new(Var,Body)|Next]):-
   findall(arg(X,Y),member(X,Var),Z),
   pasre_body(Obj_env,Memb_env,Obj,Ret,[Z|Stack],Boby),
   pasre_body(Obj_env,Memb_env,Obj,Ret,Stack,Next),!.

pasre_body(Obj_env,Memb_env,Obj,Ret,Stack,[if(Exp,Body)|Next]):-
   exp_type(Obj_env,Memb_env,Obj,Stack,Exp,bool),
   pasre_body(Obj_env,Memb_env,Obj,Ret,Stack,Body),
   pasre_body(Obj_env,Memb_env,Obj,Ret,Stack,Next),!.

pasre_body(Obj_env,Memb_env,Obj,Ret,Stack,[set(Sym,Exp)|Next]):-
   sym_type(Obj_env,Memb_env,Obj,Stack,Sym,X),
   exp_type(Obj_env,Memb_env,Obj,Stack,Exp,Y),
   assign_match(X,Y,Obj_env),
   pasre_body(Obj_env,Memb_env,Obj,Ret,Stack,Next),!.

pasre_body(Obj_env,Memb_env,Obj,Ret,Stack,[return(Exp)|_]):-
   exp_type(Obj_env,Memb_env,Obj,Stack,Exp,X),
   assign_match(Ret,X,Obj_env),!.

pasre_body(Obj_env,Memb_env,Obj,Ret,Stack,[Exp|Next]):-
   exp_type(Obj_env,Memb_env,Obj,Stack,Exp,_),
   pasre_body(Obj_env,Memb_env,Obj,Ret,Stack,Next).

exp_type(Obj_env,Memb_env,Obj,Stack,Exp,Type):-
   sym_type(Obj_env,Memb_env,Obj,Stack,Exp,Type),!.

exp_type(Obj_env,Memb_env,Obj,Stack,invoke(Inst,M,Arg),Type):-
   exp_type(Obj_env,Memb_env,Obj,Stack,Inst,T),
   belong(T,M,[Ret|ArgList],Obj_env,Memb_env),
   findtype(Obj_env,Memb_env,Obj,Stack,Arg,Y),
   findout(ArgList,Z),
   para_match(Y,Z,Obj_env),
   assign_match(Type,Ret,Obj_env),!.

findtype(_,_,_,_,[],_).
findtype(Obj_env,Memb_env,Obj,Stack,[X|Y],[Z|W]):-
   exp_type(Obj_env,Memb_env,Obj,Stack,X,Z),
   findtype(Obj_env,Memb_env,Obj,Stack,Y,W).

findout([],_).
findout([arg(_,X)|Y],[X|Z]):-findout(Y,Z).


sym_type(Obj_env,Memb_env,Obj,Stack,this,Type):-
   <:(Obj,Type,Obj_env),!.

sym_type(Obj_env,Memb_env,Obj,Stack,dot(Inst,Name),Type):-
   sym_type(Obj_env,Memb_env,Obj,Stack,Inst,T),
   belong(T,Name,Type,Obj_env,Memb_env),!.

sym_type(_,_,_,_,Name,Type):- number(Name),Type=num,!.

sym_type(_,_,_,_,Name,Type):- (Name=t;Name=f),Type=bool,!.

sym_type(_,_,_,Stack,Name,Type):-atom(Name),member(X,Stack),member(arg(Name,Sym),X),Type=Sym.

main(Prog,TypeList):-
  obj_env(Prog,Obj_env),memb_env(Prog,Memb_env),
  find_method(Memb_env,All_method),
  make_constrait_all(Obj_env,Memb_env,All_method),
  TypeList=Memb_env.
  
find_method([],_).
find_method([method(X,Y,Z,W)|Next],[method(X,Y,Z,W)|Next2]):-find_method(Next,Next2),!.
find_method([X|Next],Next2):-find_method(Next,Next2).

obj_env([],Env):-Env=[extends(bool,object),extends(num,object)].
obj_env([inherit(Sub,Super,_)|Y],Env):-obj_env(Y,Env_old),put_extends(extends(Sub,Super),Env,Env_old).

memb_env([],Env):-Env=[method(bool,compare,[bool,arg(a,bool)],[return(t)]),
                      method(num,cal,[num,arg(a,num)],[return(1)]),
                      method(num,compare,[bool,arg(a,num)],[return(t)])].
memb_env([inherit(Sub,_,Body)|Y],Env):-memb_env(Y,Env_old),helper(Sub,Body,Env,Env_old).

helper(Obj,[],Env_new,Env_old):-Env_new=Env_old.
helper(Obj,[X|Y],Env_new,Env_old):-put_mem(Obj,X,Temp,Env_old),helper(Obj,Y,Env_new,Temp).

