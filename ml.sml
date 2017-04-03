(* basis *)
signature MONAD = sig
    type 'a m
    val ret : 'a -> 'a m
    val >>= : 'a m * ('a -> 'b m) -> 'b m
end;
infixr 1 >>=;

signature MONAD_TRANS = sig
    structure m : MONAD;
    type 'a t;
    val lift : 'a m.m -> 'a t;
end;


structure identity = struct
  datatype 'a identity = identity of 'a;

  structure monad : MONAD = struct
    type 'a m = 'a identity
    fun ret a = identity a
    infix >>= fun (identity a) >>= b = b a
  end;

  open monad;
end;

structure option = struct
  fun option NONE n = SOME n
    | option (SOME x) _ = SOME x;

  structure monad : MONAD = struct
    type 'a m = 'a option
    fun ret a = SOME a
    infix >>= fun NONE   >>= _ = NONE
              | (SOME a) >>= b = b a
  end;

  functor trans(structure m : MONAD) = struct
    open m;

    datatype 'a option_trans = option_trans of ('a option) m;

    structure option_trans : MONAD_TRANS = struct
      structure m = m;
      type 'a t = 'a option_trans;
      fun lift x = option_trans (x >>= (fn x' => ret (SOME x')))
    end;

    structure monad_option_trans : MONAD = struct
      type 'a m = 'a option_trans;
      fun ret x = option_trans (m.ret (SOME x))
      infix >>= fun (option_trans a) >>= f =
        let open m in
          option_trans (a >>= (fn a' => case a' of
              NONE => ret NONE
            | SOME a'' => case f a'' of
              option_trans a''' => a'''))
        end;
    end;

    open option_trans;
    open monad_option_trans;
  end;

  open monad;  
end;

structure list = struct
  structure monad : MONAD = struct
    type 'a m = 'a list
    fun ret a = a :: []
    infix >>= fun [] >>= _ = []
                | xs >>= y = List.concat (map y xs)
  end;

  open monad;
end;
(*
functor state(eqtype s) = struct
  datatype 'a state = state of s -> s * 'a;

  fun run (state f) s = f s

  structure monad : MONAD = struct
    type 'a m = 'a state;
    fun ret a = state (fn s => (s, a));
    infix >>= fun (state f) >>= g = state (fn s => case f s of
      (s, a) => run (g a) s);
  end;

  functor trans(structure m : MONAD) = struct
    open m;

    datatype 'a state_trans = state_trans of ('a state) m;

    structure state_trans : MONAD_TRANS = struct
      structure m = m;
      type 'a t = 'a state_trans;
      fun lift x = state_trans (x >>= (fn x' => ret (monad.ret x')))
    end;

    structure monad_state_trans : MONAD = struct
      type 'a m = 'a state_trans;
      fun ret x = state_trans (m.ret (monad.ret x))
      infix >>= fun (state_trans a) >>= f =
        let open m in
          state_trans (a >>= (fn a' => 
        end;
    end;

    open state_trans;
    open monad_state_trans;
  end;
end;
*)

structure T = option.trans(structure m = identity.monad);
val transtest =
  let open T in
    let val x = ret 1 >>= (fn _ => lift (identity.monad.ret 0))
    in case x of
      option_trans x' => x'
    end
  end;

fun id x = x;

fun pi_0 ((a, _) : 'a * 'b) : 'a = a
fun pi_1 ((_, b) : 'a * 'b) : 'b = b

fun assoc ((e, l) : ''a * (''a * 'b) list) : 'b option =
    case l of
          [] => NONE
        | ((a, b) :: l') => if a = e then SOME b else assoc (e, l');

(* parsing *)
functor PARSER(eqtype t) = struct
    datatype 's parser = parser of t list -> ('s * t list) option;

    fun run (parser p : 's parser) = fn i => p i;

    fun succeed p = parser (fn i => SOME (p, i));
    val fail      = parser (fn _ => NONE);
    fun consume t = parser (fn i => case i of
          [] => NONE
        | (c :: cs) => if t = c then SOME (c, cs) else NONE);

    val done = parser (fn [] => SOME ((), [])
                        | _ => NONE);

    structure monad_parser : MONAD = struct
        type 'a m = 'a parser
        fun ret a = succeed a
        infix >>= fun (parser p) >>= q =
            let open option.monad
            in parser (fn i => p i >>= (fn (p', ps') => case q p' of
                (parser q') => q' ps'))
            end
    end;
    open monad_parser;
    infix >> fun a >> f = a >>= (fn _ => f);

    infix || fun op|| ((parser p, parser q) : 's parser * 's parser) : 's parser = parser (fn i =>
        let val ps = p i
        in case ps of
              NONE => q i
            | _  => ps
        end);
    infix && fun op&& ((p, q) : 's parser * 'u parser) : ('s * 'u) parser =
        p >>= (fn p' =>
        q >>= (fn q' =>
        ret (p', q')))

    fun disjunction (ps : ('s parser) list) : 's parser =
        case ps of
              [] => fail
            | (p :: []) => p
            | (p :: ps') => p || (disjunction ps');

    fun many (p : 's parser) : ('s list) parser =
        (p >>= (fn p' => many p >>= (fn ps' => ret (p' :: ps')))) || ret []
    fun many' (p : 's parser) : ('s list) parser =
        p      >>= (fn p' =>
        many p >>= (fn ps' =>
        ret (p' :: ps')))

    fun tokens (ts : t list) : (t list) parser =
        case ts of
              [] => ret []
            | (t :: ts) =>
                consume t >>= (fn t' =>
                tokens ts >>= (fn ts' =>
                ret (t' :: ts')))

    fun separator (s : 's parser) (p : 'v parser) : ('v list) parser =
        separator' s p || p >>= (fn p' => ret [p'])
    and separator' (s : 's parser) (p : 'v parser) : ('v list) parser =
        many (p >>= (fn p' => s >> ret p')) >>= (fn ps =>
        p                                   >>= (fn p  =>
        ret (ps @ [p])));

    fun between (d : 's parser) (p : 'v parser) (b : 'u parser) : 'v parser =
        d >> p >>= (fn p' => b >> ret p')
end;
structure PARSER_CHAR = PARSER(type t = char);

structure DATATYPES = struct
    datatype typo =
          INT_T
        | VARIABLE      of string
        | FUNCTION      of typo * typo;

    datatype atom =
          INT_A         of int
    and 'a expression =
          ATOM_E        of 'a * atom
        | IDENTIFIER    of 'a * string
        | LAMBDA        of 'a * (pattern * 'a expression) list
        | APPLICATION   of 'a * 'a expression * 'a expression
        | LET           of 'a * 'a declaration * 'a expression
        | TYPED         of 'a * typo * 'a expression
    and pattern =
          WILDCARD
        | ATOM_P        of atom
        | BINDING       of string
        | CONSTRUCTOR   of string * pattern
    and 'a declaration =
          VALUE         of string * 'a expression;

    type 'a program = ('a declaration) list;

    fun project e = case e of
          ATOM_E      (a, _)    => a
        | IDENTIFIER  (a, _)    => a
        | APPLICATION (a, _, _) => a
        | LAMBDA      (a, _)    => a
        | LET         (a, _, _) => a
        | TYPED       (a, _, _) => a;

    fun typoToString t = case t of
          INT_T => "INT_T"
        | VARIABLE s => "VARIABLE " ^ s
        | FUNCTION (a, s) => typoToString a ^ " -> " ^ typoToString s;
end

structure ML_PARSER = struct
    type a = unit;
    val (a : a) = ();

    open DATATYPES;

    infixr ||;
    infixr &&;
    open PARSER_CHAR;
    infix >> fun a >> f = a >>= (fn _ => f);
    fun run p s = PARSER_CHAR.run p (String.explode s);
    fun char c = consume c;
    fun string s =
        tokens (String.explode s) >>= (fn s' =>
        ret (String.implode s'))

    fun parentheses p = between (char #"(") p (char #")");

    val space = char #" "  ||
                char #"\t" ||
                char #"\n";
    val spaces = many space;
    val spaces' = many' space;

    val numeral = disjunction (map char (String.explode "0123456789"));
    val letter = disjunction (map char (String.explode "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"));
    val symbol = disjunction (map char (String.explode "~!@#$%^&*[]_+`-=(){}\\\"|;',./<>?"));

    val number = disjunction [char #"0" >> ret 0,
                      char #"1" >> ret 1,
                      char #"2" >> ret 2,
                      char #"3" >> ret 3,
                      char #"4" >> ret 4,
                      char #"5" >> ret 5,
                      char #"6" >> ret 6,
                      char #"7" >> ret 7,
                      char #"8" >> ret 8,
                      char #"9" >> ret 9];

    val int =
        many' number >>= (fn ns =>
        let fun pow (b, 0) = 1
              | pow (b, e) = b * pow (b, e - 1)
            fun c ([], _) = 0
              | c ((n :: ns), e) = n * pow(10, e) + (c (ns, (e + 1)))
        in ret (c (List.rev ns, 0))
        end);

    val alphanumeric = many' (letter || numeral);

    val atom = int >>= (fn n => ret (INT_A n));

    val identifier =
        letter                   >>= (fn c  =>
        many (letter || numeral) >>= (fn cs =>
        ret (String.implode (c :: cs))));

    fun pattern _ =
        spaces >>
        disjunction [char #"_"  >>
                     ret WILDCARD,
                     atom       >>= (fn a =>
                     ret (ATOM_P a)),
                     identifier >>= (fn i =>
                     ret (BINDING i)),
                     identifier >>= (fn i =>
                     pattern () >>= (fn p =>
                     ret (CONSTRUCTOR (i, p)))),
                     char #"("  >>
                     identifier >>= (fn i =>
                     pattern () >>= (fn p =>
                     char #")"  >>
                     ret (CONSTRUCTOR (i, p))))];

    fun expression _ =
        disjunction [atom       >>= (fn a => ret (ATOM_E   ((), a))),
                     lambda (),
                     identifier >>= (fn i => ret (IDENTIFIER ((), i)))]
    and lambda _ =
        string "fn"            >>
        spaces'                >>
        bindings (string "=>") >>= (fn bs =>
        ret (LAMBDA ((), bs)))
    and bindings a = 
        separator (spaces        >>
                   char #"|"     >>
                   spaces)
                  (pattern ()    >>= (fn p =>
                   spaces        >>
                   a             >>
                   spaces        >>
                   expression () >>= (fn e =>
                   ret (p, e))));

    val function =
        string "fun" >>
        spaces'      >>
        identifier   >>= (fn i =>
        spaces'      >>
        bindings (string "=") >>= (fn bs =>
        ret (VALUE (i, (LAMBDA ((), bs))))));

    val value =
        string "val"  >>
        spaces'       >>
        identifier    >>= (fn i =>
        spaces        >>
        char #"="     >>
        spaces        >>
        expression () >>= (fn b =>
        ret (VALUE (i, b))));

    val declaration : (a declaration) parser = function || value;
    fun parse (i : string) : (a program) option =
        case run (separator (spaces >> char #";" >> spaces) declaration >>= (fn ds => done >> ret ds)) i of
              NONE => NONE
            | SOME (p, _) => SOME p;
end;

structure INFERENCE = struct
open DATATYPES;

open option;

type Context = (string * typo) list;

(* unification and type inference *)
fun resolve ((i, c) : string * Context) : typo option = case c of
      [] => NONE
    | ((i', t) :: c') =>
        if i = i'
            then case t of
                  VARIABLE i'' => resolve (i'', c')
                | _ => SOME t
            else
                resolve (i, c')

fun unify ((a, b, c) : typo * typo * Context) : Context option = case (a, b) of
      (VARIABLE i, _) => (case resolve (i, c) of
          NONE => SOME ((i, b) :: c)
        | SOME t => unify (t, b, c))
    | (_, VARIABLE _) => unify (b, a, c)
    | (FUNCTION (a, s), FUNCTION (a', s')) => (case unify (a, a', c) of
          NONE => NONE
        | SOME c' => unify (s, s', c'))
    | (INT_T, INT_T) => SOME c
    | (_, _) => NONE;

fun infer (p : 'a program) : (typo program) option = case infer' (p, [], []) of
      NONE => NONE
    | SOME (p', _, _) => SOME p'
and infer' (p, c, is) = case p of
      [] => ret ([], c, is)
    | (d :: ds) =>
        declaration (d, c, is) >>= (fn (d', c', is') =>
        infer' (ds, c', is')   >>= (fn (ds, c, is) =>
        ret (d' :: ds, c, is)))
and declaration (VALUE (i, e), c, is) =
    let val i' = new (map pi_0 c)
    in expression (e, (i', VARIABLE i') :: c, is) >>= (fn (e', c', is') =>
       unify (project e', VARIABLE i', c') >>= (fn c'' =>
       ret (VALUE (i, e'), c'', (i, i') :: is)))
    end
and expression (e, c, is) = case e of
      ATOM_E (_, a) =>
        ret (ATOM_E (atom a, a), c, is)
    | IDENTIFIER (_, i)  =>
        assoc (i, is) >>= (fn i' =>
        ret (IDENTIFIER (VARIABLE i', i), c, is))
    | LAMBDA (_, bs) =>
        let val pi = new (map pi_0 c)
            val ei = new (pi :: map pi_0 c)
            val pv = VARIABLE pi
            val ev = VARIABLE ei
            fun s (bs, c, is) = (case bs of
                  [] => ret ([], c, is)
                | ((p, e) :: bs') =>
                    pattern (p, c, is)           >>= (fn (p', c', is') =>
                    expression (e, c', is')      >>= (fn (e', c'', is'') =>
                    unify (p', pv, c'')          >>= (fn c''' =>
                    unify (project e', ev, c''') >>= (fn c'''' =>
                    s (bs', c'''', is'')         >>= (fn (bs, c, is) =>
                    ret (bs @ [(p, e')], c, is)))))))
        in s (bs, (pi, pv) :: (ei, ev) :: c, is) >>= (fn (bs', c', is') =>
           option (resolve (pi, c')) pv >>= (fn pv =>
           option (resolve (ei, c')) ev >>= (fn ev =>
           ret (LAMBDA (FUNCTION (pv, ev), List.rev bs'), c', is'))))
        end
    | APPLICATION (_, a, b) =>
        expression (a, c, is)   >>= (fn (a', c', is')   =>
        expression (b, c', is') >>= (fn (b', c'', is'') =>
        let val an = new (map pi_0 c'')
            val su = new (an :: (map pi_0 c''))
            val av = VARIABLE an
            val sv = VARIABLE su
        in unify (project a', FUNCTION (av, sv), c'') >>= (fn c''' =>
           ret (APPLICATION (project b', a', b'), (an, av) :: (su, sv) :: c''', is''))
        end))
    | LET (_, d, e) =>
        declaration (d, c, is)  >>= (fn (d', c', is') =>
        expression (e, c', is') >>= (fn (e', c'', is'') =>
        ret (LET (project e', d', e'), c'', is'')))
    | TYPED (_, t, e) =>
        expression (e, c, is)     >>= (fn (e', c', is') =>
        unify (project e', t, c') >>= (fn c''           =>
        ret (TYPED (t, t, e'), c'', is')))
and atom (INT_A _) = INT_T
and pattern (p, c, is) = case p of
      WILDCARD =>
        let val i = new (map pi_0 c)
        in ret (VARIABLE i, (i, VARIABLE i) :: c, is)
        end
    | BINDING i =>
        let val i' = new (map pi_0 c)
        in ret (VARIABLE i', (i', VARIABLE i') :: c, (i, i') :: is)
        end
    | ATOM_P a => ret (atom a, c, is)
and new (ss : string list) : string = new' (ss, 0)
and new' ((ss, n) : string list * int) : string =
    let val i = "t" ^ Int.toString n
    in case ss of
          [] => i
        | (s :: ss') => if s = i then new' (ss, n + 1) else new' (ss', n)
    end
end;

structure INTERPRETER = struct
    open option.monad;
    open DATATYPES;

    fun interpret (p : 'a program) : ('a program) option = case p of
          [] => ret []
        | (d :: ds) => declaration d >>= (fn d' =>
                       interpret ds  >>= (fn ds' =>
                       ret (d' :: ds')))
    and declaration (VALUE (i, b)) =
        expression b >>= (fn b' =>
        ret (VALUE (i, b')))
    and expression (e : 'a expression) : ('a expression) option = case e of
          APPLICATION (_, (LAMBDA (_, bs)), r) =>
            expression r >>= (fn r' =>
            match bs r)
        | _ => ret e
    and match [] e : ('a expression) option = NONE
      | match ((p, b) :: bs) e =
        case (p, e) of
              (WILDCARD, _) => ret b
            | (ATOM_P p, ATOM_E (_, q)) => if p = q then ret b else match bs e
(*            | (BINDING i, b) =>  *)
            | _ => match bs e
    and substitute v b e = ();
end;

structure TEST = struct
    fun test ts = map (fn (t, r) => t = r) ts
    val run =
          test
            let open ML_PARSER in
                map (fn (a, s) => (parse a, s))
                    [("val x = 0", SOME [VALUE ("x", ATOM_E ((), INT_A 0))]),
                     ("val f = fn 0 => 1 | _ => 2", SOME [VALUE ("f", LAMBDA ((), [(ATOM_P (INT_A 0), ATOM_E ((), INT_A 1)), (WILDCARD, ATOM_E ((), INT_A 2))]))])]
            end
        @ test
            let open ML_PARSER
                open INFERENCE in
                map (fn (a, s) => (parse a >>= infer, s))
                    [("val f = fn 0 => 1 | _ => 0", SOME [VALUE ("f", LAMBDA (FUNCTION (INT_T, INT_T), [(ATOM_P (INT_A 0), ATOM_E (INT_T, INT_A 1)), (WILDCARD, ATOM_E (INT_T, INT_A 0))]))])]
            end
end;

val _ = print "hello, world!\n";

id TEST.run;
