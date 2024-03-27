module Main exposing (..)

import Browser
import Html exposing (Html, button, div, text, table, tr, td, textarea, span, input, label, form)
import Html.Events exposing (onClick, onInput, onCheck)
import Html.Attributes exposing (id, colspan, rowspan, style, placeholder, value, size, disabled, class, spellcheck, type_, checked, method, name, action)
import List exposing (filter, intersperse, length, head, tail,  map, member, all, foldl, reverse, concat, take, drop)
import Debug exposing (toString)
import Html.Parser
import Html.Parser.Util
import Result exposing (withDefault)
import Tuple exposing (first, second)
import Set
import Parser exposing (Parser, (|.), (|=),backtrackable)
import Pratt
import String exposing (replace, fromInt)
import Tuple exposing (pair)


-- MAIN

main : Program () Model Msg
main =
  Browser.element
    { init = init
    , update = update
    , view = view
    , subscriptions = subscriptions
    }



-- MODEL


type alias Model =
  { tree:Tree
  , tNote:String
  , input: String
  , iNote:String
  , showTreeUI:Bool
  , steps: List {correct: Bool, subs: List (Int,Type), tree: Tree}
  , stepIndex: Int
  , vars: List String
  , typeVars: List (Int,Type)
  , displayRules: Bool
  , shortContext: Bool
  }

type Tree = Tree {parent: (Context,Term), children: Children, ruleName: String}
type Children
  = Node (List Tree)
  | Leaf
  | LeafC Int Type Context
  | TypeErr String

type Type
  = TFree String
  | TInf Int
  | Fun Type Type

type Info
  = HasType Type
--  | SuppotedType 

type alias Context = List (Int, Info)

type Term
  = Ann Term Type
  | Var Int
  | Lam Int Type Term
  | App Int Term Term
  | Cond Term Term Term
  | Int Int
  | Bool Bool




init :() -> (Model, Cmd Msg)
init _ =
  let
    testStr = "x0:Int→Int→Bool, x1:Bool, xyz:Int ⊢ λy:Int.if (x0 7 13) then y else 0 5 : Int"
    _ = Debug.log "help" (testStr)
  in
  ( { tree= Tree {
         parent=
          ([],Ann 
            (Bool False)
            (TFree "Bool")
          )
        ,children=Node []
        ,ruleName=""
      }
    , tNote=""
    , input=""
    , iNote=""
    , showTreeUI=False
    , steps=[]
    , stepIndex=1
    , vars=[]
    , typeVars=[]
    , displayRules = True
    , shortContext = True
    }
  , Cmd.none
  )


makeAssumptions : (Context,Term) -> (Children,List (Int,Type),String)
makeAssumptions (c,t) =
  case t of
    Ann term ty ->
      case term of
        App n fTerm pTerm->
           ((Node
            [Tree {parent=(c,Ann fTerm (Fun (TInf n) ty)),children=(Node []),ruleName=""}
            ,Tree {parent=(c,Ann pTerm (TInf n)),children=(Node []),ruleName=""}
            ]),[],"APP")
        Int _->
          if ty==(TFree "Nat")
            then (Leaf,[],"NAT")
            else (TypeErr ("Found 'Int' constant but expected type '"++showType ty++"'"),[],"NAT Err")
        Bool _->
          if ty==(TFree "Bool")
            then (Leaf,[],"BOOL")
            else (TypeErr ("Found 'Bool' constant but expected type '"++showType ty++"'"),[],"BOOL Err")
        Var n  ->
          case (lookUp n c) of
            Just temp ->
              let
                found = (\(HasType x)->x) temp
                (good,subs)= typeCompare ty found
              in
              if good 
                then ((LeafC n ty c),subs,"VAR")
                else (TypeErr ("Found '"++showType found++"' but expected type '"++showType ty++"'"),subs,"VAR Err")
            Nothing -> (TypeErr "Variable is NOT in the context",[],"VAR Err")
        Cond cond b1 b2 ->
           ((Node
            [Tree {parent=(c,Ann cond (TFree "Bool")),children=(Node []),ruleName=""}
            ,Tree {parent=(c,Ann b1 ty),children=(Node []),ruleName=""}
            ,Tree {parent=(c,Ann b2 ty),children=(Node []),ruleName=""}
            ]),[],"IF")
        Lam n varTy t1 ->
          case ty of
            Fun ty1 ty2 ->
              let
                (good,subs) = typeCompare ty1 varTy
              in
              if good
                then ((Node
                  [Tree {parent=(c++[(n,HasType varTy)],Ann t1 ty2),children=(Node []),ruleName=""}]),subs,"ABS")
                else
                  (TypeErr "Lambda parameter and lambda type mismatch",subs,"ABS Err")
            _ ->
              (TypeErr ("Expected nonfunctional type '"++showType ty++"' but found functional type (lambda abstraction)"),[],"ABS Err")
        _ ->
          (TypeErr "No rule found",[],"Err")
        
    _ ->
      (TypeErr "The term needs to be an annotation",[],"Err")

expandStepped : Tree -> List (Int,Type) -> List {tree: Tree,correct: Bool, subs: List (Int,Type)}
expandStepped (Tree tree) passedTypeVars=
  let
    substitutedP = ((\(Tree t) -> t) (typeSub (Tree tree) passedTypeVars)).parent
    (assums,assTypeVars,rule)= makeAssumptions substitutedP
    allTypeVars = passedTypeVars++assTypeVars  --known type var substitutions (passed and from assumtions/rule)
  in
  case assums of
    TypeErr str ->
      [{tree= Tree {parent=tree.parent , children=TypeErr str, ruleName=rule}, correct= False, subs= allTypeVars}]
    (Node list) ->
      let
        gradualEx = foldl 
          (\child accum -> case reverse accum of
            [] -> [expandStepped child allTypeVars]
            c::_ -> case reverse c of
              [] ->
                [expandStepped child allTypeVars]
              recent::_ ->
                accum ++ [expandStepped child recent.subs]
          ) 
          []
          list
        chLastStepTrees = map
          (\steps ->
            case reverse steps of
              [] ->
                Tree  { parent=([],Int (-1))
                      , children=TypeErr "Internal Error! (please report this to feedback, if you get this error)"
                      , ruleName=""}
              last::_ ->
                last.tree
          )
          gradualEx
        childrenSteps = List.map2
          (\steps i ->
            map
              (\step ->
                let
                  newChildren = (take i chLastStepTrees) ++ [step.tree] ++ (drop (i+1) list)
                in
              {step | tree = (Tree {parent=tree.parent, children = Node newChildren,ruleName=rule})}
              )
              steps
          )
          gradualEx
          (List.range 0 ((length list)-1))
        laterSteps = concat childrenSteps
        baseStep = {tree= Tree {parent=tree.parent, children=Node list, ruleName=rule}, correct=  True, subs= allTypeVars}
      in
      baseStep::laterSteps
    someLeaf ->
      [{tree= Tree {parent=tree.parent, children=someLeaf, ruleName=rule},   correct=  True, subs= allTypeVars}]

typeSub : Tree -> List (Int,Type) -> Tree
typeSub (Tree t) subs= 
  case second t.parent of
    Ann t1 ty ->
      let
        tySub ty0= 
          case ty0 of
            TInf n ->
              Maybe.withDefault ty0 (lookUp n subs)
            Fun ty1 ty2 ->
              Fun (tySub ty1) (tySub ty2)
            _ -> ty0
      in
      Tree {t | parent=(first t.parent,Ann t1 (tySub ty))}
    _ -> Tree t
    
typeCompare : Type -> Type -> (Bool,List (Int,Type))
typeCompare expected found=
  let
    _ = Debug.log "found" found
  in
  case (Debug.log "expected" expected) of
    TFree ty ->
      if found==expected
        then (True,[])
        else (False,[])
    TInf i ->
      (True,[(i,found)])
    Fun ty1 ty2 ->
      case found of
        Fun tyX tyY ->
          let
            (b1,s1) = typeCompare ty1 tyX
            (b2,s2) = typeCompare ty2 tyY
          in
          (b1&&b2,s1++s2)
        _ ->
          (False,[])


-- UPDATE

type Msg
  = Reset
  | ExpandWhole
  | StepForward
  | StepBack
  | ChangeInput String
  | SubmitInput
  | SetShortContext Bool
  | SetDisplayRules Bool


update : Msg -> Model -> (Model,Cmd Msg)
update msg model =
  let
    defStep = {tree= Tree {parent=([],Bool False) ,children=Node [],ruleName=""},correct= False, subs= []}
    getStep n = Maybe.withDefault (defStep) (selectStep n model.steps)
  in
  case msg of
    Reset ->
      let
        step = getStep 1
        t  = step.tree
        s  = step.subs
      in
      ({model | tree=t,typeVars=s,stepIndex=1},Cmd.none)
    StepForward ->
      let
        allowed = model.stepIndex < (length model.steps)
        i = model.stepIndex+1
        step = getStep i
        t  = step.tree
        s  = step.subs
      in
      if allowed
        then ({model | tree=t,typeVars=s,stepIndex=i},Cmd.none)
        else (model,Cmd.none)
    StepBack ->
      let
        allowed = model.stepIndex > 1
        i = model.stepIndex-1
        step = getStep i
        t  = step.tree
        s  = step.subs
      in
      if allowed
        then ({model | tree=t,typeVars=s,stepIndex=i},Cmd.none)
        else (model,Cmd.none)
    ExpandWhole ->
      let
        i = length model.steps
        step = getStep i
        t  = step.tree
        s  = step.subs
      in
      ({model | tree=t,typeVars=s,stepIndex=i},Cmd.none)
    ChangeInput newInput ->
      let
        myReplace (keyword,value) str = replace keyword value str
        replacements = [("|-", "⊢"),("\\l","λ"),("->","→")]
        processedInput =
          foldl myReplace newInput replacements 
      in
      ({ model | input = processedInput },Cmd.none)
    SubmitInput ->
      let
        processedInput = processProgramInput model.input
        newSteps r = Debug.log
                        "steps"
                        ((firstStep r)::(expandStepped (firstStep r).tree []))
        firstStep r = {tree=Tree{parent=r,children=Node [],ruleName=""},correct=True,subs=[]}
      in
      case processedInput of
        Ok (root,vars) ->
          ({model | typeVars= [],
                    tree = (firstStep root).tree,
                    iNote= "",
                    showTreeUI= True,
                    steps= newSteps root,
                    stepIndex= 1,
                    vars= vars
           }
          ,Cmd.none
          )
        Err str ->
          ({model | iNote=str,
                    showTreeUI=False,
                    tNote=""
           }
          ,Cmd.none
          )
    SetShortContext b ->
      let
        _ = Debug.log "substitute context: " b
      in
      ({model | shortContext = b},Cmd.none)
    SetDisplayRules b ->
      let
        _ = Debug.log "display rules: " b
      in
      ({model | displayRules = b},Cmd.none)

selectStep : Int -> List {tree: Tree,correct: Bool, subs: List (Int,Type)} -> Maybe {tree: Tree,correct: Bool, subs: List (Int,Type)}
selectStep i list =
  if (i <= 1)
    then head list
    else (tail list) |> Maybe.andThen (selectStep (i-1))




-- VIEW


view : Model -> Html Msg
view model =
  let
    dui = not model.showTreeUI
    low = model.stepIndex == 1
    high= model.stepIndex == (length model.steps)
    typeVarsVisible=model.showTreeUI && model.typeVars/=[]
    stepCount = (fromInt model.stepIndex) ++ "/" ++ (fromInt (length model.steps))
  in
  div [ class "page" ]                                --Page 
      [ div
          [ id "overlay" ]
          [ div [ id "overlay_background"] []
          , div [ class "window"]
                [ form  [ id "report_form"
                        , method "POST"
                        , action "report-form.php"
                        ]
                        [ label []
                                [ text "Description:"
                                , input [name "message"][]
                                ]
                        , input [ type_ "submit"
                                , value "send"
                                ]
                                []
                        ]
                ]
          ]
      , div 
          [ class "header" ]                          --Header
          [ div []
                [ button [ id "report_button"] [] ]
          , div [ class "title"]                                    --Name 
                [ span  [ class "logo" ] 
                        [text "λ"]
                , span  []
                        [text "CALCULUS TypeChecker"]
                ]
          ]
      , div                                           --App
          [ class "app" ]
          [ div [class "program_input" ]              --Program input 
                [(textarea[ placeholder "Enter your program"
                          , spellcheck False
                          , value model.input
                          , onInput ChangeInput
                          ]
                          []
                  )
                , (button [ onClick SubmitInput ] [text "↲"])
                ]
          , div [ class "parse_note" ]                --Parsing error
                [ if model.iNote==""
                    then
                      div [ class "no_err" ][]
                    else
                      div [ class "err" ]
                          [ span [] [text "Parse Error:"]
                          , div  [] [text model.iNote]
                          ]
                ]
          , div ([ class "zoom" ]                  --zoom panel 
                  ++if dui then [class "off"] else []
                ) 
                [ div
                  []
                  [ (button [disabled (dui), id "zoom_minus"] [ text "-" ])
                  , span 
                    []
                    [text "zoom"]
                  , (button [disabled (dui), id "zoom_plus"] [ text "+" ])
                  ]
                ]
          , div ([ class "tree" ]                     --Tree
                  ++if dui then [class "off"] else []
                ) 
                [ div []
                      [ if model.showTreeUI
                          then
                            showTree 
                              model.tree
                              model.vars
                              model.displayRules
                              (if model.shortContext
                                then
                                  Just ([],0)
                                else
                                  Nothing
                              )
                          else div [] []
                      ]
                ]
          , div ([ class "control" ]                  --control panel 
                  ++if dui then [class "off"] else []
                ) 
                [ div
                  []
                  [ (label  []
                            [ text "short context"
                            , input [ onCheck SetShortContext
                                    , disabled dui
                                    , type_ "checkbox"
                                    , checked model.shortContext
                                    ]
                                    []
                            ]
                    )
                  , (button [ onClick Reset   , disabled (dui || low)] [ text "<<" ])
                  , (button [ onClick StepBack, disabled (dui || low)] [ text "<"  ])
                  , span 
                    []
                    [ if dui
                        then (text "-/-")
                        else (text stepCount)
                    ]
                  , (button [ onClick StepForward, disabled (dui || high)] [ text ">" ])
                  , (button [ onClick ExpandWhole, disabled (dui || high)] [ text ">>"])
                  , (label  []
                            [ text "show rules"
                            , input [ onCheck SetDisplayRules
                                    , disabled dui
                                    , type_ "checkbox"
                                    , checked model.displayRules
                                    ]
                                    []
                            ]
                    )
                  ]
                ]
          , div [] [ text model.tNote ]               --Note
          , div [ class "type_vars" ]                 --Values of type variables
                [ div [] [ text "Type variables:" ]
                , if (typeVarsVisible)
                    then
                      div []
                          (showTypeVars model.typeVars)
                    else
                      div [ class "off" ][]
                ]
                
                
          ]
      ]

showTree : Tree -> List String-> Bool -> Maybe (List (Int,Context),Int) -> Html Msg
showTree (Tree t) vars displayRules contextSubs =
  first (showTree_Next (Tree t) vars displayRules contextSubs)



showTree_Next : Tree -> List String-> Bool -> Maybe (List (Int,Context),Int) -> (Html Msg,Int)
showTree_Next (Tree t) vars displayRules contextSubs =
  let
    ws = case (withDefault [] (Html.Parser.run "<td> &emsp; </td>") |> Html.Parser.Util.toVirtualDom) of
      x::xs -> x
      [] -> td [] [text " "]
    getNext s = 
      case s of 
        Just (_,n) -> n
        Nothing -> -1
  in
  case (t.children) of
    Node [] ->
      let
        (c,s)= showContext (first t.parent) vars contextSubs
      in
      pair
        (text (c ++" ⊢ "++ showTerm (second t.parent) vars))
        (getNext s)
    _ ->
      let
        (context,newSubs)=showContext (first t.parent) vars contextSubs
        childrenFold ch =
          foldl
            (\a b -> 
              let
                s=case (head(reverse b)) of
                  Nothing->newSubs
                  Just (_,n)-> case newSubs of
                    Nothing -> Nothing
                    Just ns -> Just (first ns,n)
              in
              b++[showTree_Next a vars displayRules s]
            )
            []
            ch
      in
      pair
        (table
          []
          [ tr [] ((case (t.children) of
                    LeafC var ty c ->
                      [text ( showTerm (Var var) vars ++ ":" ++ showType ty ++ " ∈ " ++ first (showContext c vars newSubs))]
                    Node children ->
                      intersperse
                        ws
                        (map
                          (\(x,_)->td [] [x])
                          (childrenFold children)
                        )
                    TypeErr str -> [ span [] [text str] ]
                    _ -> [ws]
                  )++if displayRules then [td [rowspan 2, class "rule"][text ("("++t.ruleName++")")]] else [])
          , tr []
              [ td (case (t.children) of  
                     Node children -> [colspan ((length children)*2-1)]
                     _ -> []
                   )
                   [text (context ++" ⊢ "++ showTerm (second t.parent) vars)]
              ]
          ]
       )
        (case  t.children of
          Node ch ->
            case (head(reverse (childrenFold ch))) of
              Nothing->  -1
              Just (_,n)-> n
          _ ->  
            getNext newSubs
        )


showTerm : Term -> List String -> String
showTerm t v =
  let
    priority term =
      case term of
        Lam _ _ _ -> 1
        App _ _ _ -> 2
        Cond _ _ _-> 1
        _ -> 0

    isOpenEnded term =
      case term of
        Lam _ _ _ ->True
        Cond _ _ _->True
        _ -> False
  in
  case t of
    Ann term ty ->
      (showTerm term v)++":"++(showType ty)
    Var n ->
      case (atIndex n v) of
        Just str -> str
        Nothing  -> "var"++(fromInt n)
    Lam n ty term ->
      "λ"++showTerm(Var n) v++":"++(showType ty)++"."++(showTerm term v)
    App _ t1 t2 ->
      (
        if isOpenEnded t1
        then
          "("++(showTerm t1 v)++")"
        else
          (showTerm t1 v)
      )
      ++
      (
        if priority t2 >= 2
        then
          " ("++(showTerm t2 v)++")"
        else
          " "++(showTerm t2 v)
      )
    Cond c t1 t2 ->
      "if "++showTerm c v++" then "++showTerm t1 v++" else "++showTerm t2 v
    Int n -> fromInt n
    Bool b-> case b of 
      True -> "true"
      False -> "false"

showType : Type -> String
showType t =
  case t of
    TFree str ->
      str
    Fun t1 t2 ->
      case t1 of
        Fun _ _ ->
          "("++(showType t1)++")→"++(showType t2)
        _ ->
          (showType t1)++"→"++(showType t2)
    TInf n  ->
      "T"++fromInt n

showContext : Context -> List String -> Maybe (List (Int,Context),Int) -> (String,Maybe (List (Int,Context),Int))
showContext c v cs =
  let
    toStr n =
      case (atIndex n v) of
        Just str -> str
        Nothing  -> "var"++(fromInt n)
    showNormal con =
      (case con of
          [] -> ""
          (n,HasType t)::[]-> (toStr n)++":"++(showType t)
          (n,HasType t)::l -> (toStr n)++":"++(showType t)++", "++(showNormal l)
      )
    toSubscript n =
      let
        delta = (Char.toCode '₀')-(Char.toCode '0')
      in
      String.fromList
        (map (\x -> Char.fromCode ((Char.toCode x) + delta)) (String.toList (fromInt n)))

  in
  case cs of
    Nothing ->
      pair
        (showNormal c)
        cs
    Just (subs,next) ->
      let
        shiftR l r = (take ((length l) - 1) l,(drop ((length l)-1) l) ++ r )
        matchBiggest context out=
          case (getIndex context subs) of
            Nothing ->
              let
                (l,r) =  Debug.log "shifted into" (shiftR context out)
              in
              if l == []
                then
                  (-1,r)
                else
                  matchBiggest l r
            Just s ->
              (s,out)
        (sub,leftout) = matchBiggest c []
        anyLeft = leftout /=[]
        newCs = if anyLeft then Just (subs ++ [(next,c)],next+1) else cs
      in
      pair 
        (
          if sub == -1
            then
              showNormal leftout
          else
            "Γ"++
            (toSubscript sub)++
            (if anyLeft then ", "++(showNormal leftout) else "")
        )
        newCs


showTypeVars : List (Int,Type) -> List (Html Msg)
showTypeVars vars =
  map (\(n,t) ->
        div [] [text ( (showType (TInf n))++" = "++(showType t) )] 
      )
      vars



getIndex :  b -> List (a,b) -> Maybe a
getIndex a l =
  let
    found = filter (\x->second x == a) l
  in
  Maybe.map first (head found)

lookUp :  a -> List (a,b) -> Maybe b
lookUp a l =
  let
    found = filter (\x->first x == a) l
  in
  Maybe.map second (head found)

atIndex : Int -> List a -> Maybe a
atIndex a l =
  let
    li=List.indexedMap (\i e-> (i,e)) l
  in
    lookUp a li

-- SUBSCRIPTIONS
subscriptions: Model -> Sub Msg
subscriptions _ =
  Sub.none


-- PARSING

type alias ParsedContext = List (String,Type)
type ParsedTerm
  = VarPT String
  | LamPT String Type ParsedTerm
  | AppPT ParsedTerm ParsedTerm
  | CondPT  ParsedTerm ParsedTerm ParsedTerm
  | IntPT Int
  | BoolPT Bool

programP : Parser (ParsedContext,ParsedTerm,Type)
programP = 
  Parser.oneOf
    [ contextProgramP
    , noncontextProgramP
    ]

contextProgramP : Parser (ParsedContext,ParsedTerm,Type)
contextProgramP = 
  let
    tp = Debug.log "parsing" termP
  in
  Parser.succeed (\c te ty -> (c,te,ty)) 
    |= contextP 
    |. Parser.spaces
    |. Parser.symbol "⊢"
    |. Parser.spaces
    |= tp--termP
    |. Parser.spaces
    |. Parser.symbol ":"
    |. Parser.spaces
    |= typeP
    |. Parser.end

noncontextProgramP : Parser (ParsedContext,ParsedTerm,Type)
noncontextProgramP = 
  Parser.succeed (\te ty -> ([],te,ty)) 
    |= termP
    |. Parser.spaces
    |. Parser.symbol ":"
    |. Parser.spaces
    |= typeP
    |. Parser.end

contextP : Parser ParsedContext
contextP =
  Parser.sequence
    { start = ""
    , separator = ","
    , end = ""
    , spaces = Parser.spaces
    , item = contextItemP
    , trailing = Parser.Optional
    }

contextItemP : Parser (String,Type)
contextItemP =
  Parser.succeed (\n t -> (n,t))
    |= varP
    |. Parser.spaces
    |. Parser.symbol ":"
    |. Parser.spaces
    |= typeP

varP : Parser String
varP =
  Parser.variable
    { start = Char.isLower
    , inner = \c -> Char.isAlphaNum c || c=='_'
    , reserved = Set.fromList ["λ","if","then","else","true","false"]
    }


typeP : Parser Type
typeP =
  Pratt.expression
    { oneOf = 
      [ Pratt.constant (Parser.keyword "Nat") (TFree "Nat")
      , Pratt.constant (Parser.keyword "Bool") (TFree "Bool")
      , brcType
      ]
    , andThenOneOf = [ Pratt.infixRight 10 (Parser.symbol "→") (Fun) ]
    , spaces = Parser.spaces}

brcType : Pratt.Config Type -> Parser Type
brcType config =
  Parser.succeed identity
      |. Parser.symbol "("
      |= Pratt.subExpression 0 config
      |. Parser.symbol ")"

termP : Parser ParsedTerm
termP =
  Pratt.expression
    { oneOf =
      [ condTerm 
      , Pratt.constant (Parser.keyword "true") (BoolPT True)
      , Pratt.constant (Parser.keyword "false") (BoolPT False)
      , Pratt.literal (Parser.succeed VarPT |= varP)
      , lamTerm
      , brcTerm
      , Pratt.literal (Parser.succeed IntPT |= (backtrackable Parser.int))
      ]
    , andThenOneOf =
        [ Pratt.infixLeft 5 (Parser.symbol "") (AppPT)
        ]
    , spaces = Parser.spaces}

brcTerm : Pratt.Config ParsedTerm -> Parser ParsedTerm
brcTerm config =
  let 
    _ = Debug.log "bracket term parser" config
  in
  Parser.succeed identity
    |. Parser.symbol "("
    |= Pratt.subExpression 0 config
    |. Parser.symbol ")"

condTerm : Pratt.Config ParsedTerm -> Parser ParsedTerm
condTerm config =
  let 
    _ = Debug.log "condition term parser" config
  in
  Parser.succeed CondPT
    |. Parser.keyword "if"
    |. Parser.spaces
    |= Pratt.subExpression 3 config
    |. Parser.spaces
    |. Parser.keyword "then"
    |. Parser.spaces
    |= Pratt.subExpression 3 config
    |. Parser.spaces
    |. Parser.keyword "else"
    |. Parser.spaces
    |= Pratt.subExpression 3 config

lamTerm : Pratt.Config ParsedTerm -> Parser ParsedTerm
lamTerm config = 
  let 
    _ = Debug.log "lambda term parser" config
  in
  Parser.succeed LamPT
    |. Parser.symbol "λ"
    |. Parser.spaces
    |= varP
    |. Parser.spaces
    |. Parser.symbol ":"
    |. Parser.spaces
    |= typeP
    |. Parser.spaces
    |. Parser.symbol "."
    |. Parser.spaces
    |= Pratt.subExpression 1 config


parse : String -> Result String (ParsedContext,ParsedTerm,Type)
parse input =
  Result.mapError toString (Parser.run programP input)

processProgramInput : String -> Result String ((Context,Term),List String)
processProgramInput input =
  parse input |> Result.andThen transformProgram


type alias Variables = List String

transformProgram : (ParsedContext,ParsedTerm,Type) -> Result String ((Context,Term),List String)
transformProgram (pc,pt,t) =
  let
    context = transformContext 0 pc
    nextVar = length pc
    av = map (\(v,_)->v) pc
    sv = List.indexedMap (\i e -> (i,e)) av
    transTerm = transformTIter pt av sv nextVar 0 
  in
  case transTerm of
    Result.Ok (_,_,(_,term,v)) ->
      Result.Ok ((context,Ann (term) (t)),v)
    Result.Err str ->
      Result.Err str

transformContext : Int -> ParsedContext -> Context
transformContext index pc =
  case pc of
    [] -> []
    (_,ty)::rest -> (index, HasType ty) :: transformContext (index+1) rest


transformTIter : ParsedTerm -> Variables -> List (Int,String) -> Int -> Int -> Result String (Int,Int,(List(Int,String),Term,Variables))
transformTIter pt allVars scopeVars nextVarIndex nextAppIndex =
  let
    andThenIter res nextTerm = 
      case res of
        Result.Ok (nv,na,(_,t,av)) ->
          transformTIter nextTerm av scopeVars nv na
        Result.Err str ->
          Result.Err str
    getT r = (\(_,_,(_,t,_))->t) (withDefault (0,0,([],Int 404,[])) r)
    find v l = filter (\e -> e>=0) (map (\(i,e) -> if (v==e) then i else -1) l)
  in
  case pt of
    VarPT str ->
      let
        found = find str scopeVars
      in
      case found of
        f::rest ->
          Result.Ok (nextVarIndex,nextAppIndex,(scopeVars,Var f,allVars))
        [] ->
          Result.Err ("unknown variable '"++(str)++"'")
    LamPT str ty term ->
      let
        found = find str scopeVars
        newAv = allVars ++ [str]
        newSv = scopeVars ++ [(nextVarIndex,str)]
        r = transformTIter term newAv newSv (nextVarIndex+1) nextAppIndex
      in
      case found of
        f::rest ->
          Result.Err ("variable with name '"++(str)++"' already in use in the scope of lambda")
        [] ->
          case r of
            Result.Ok (nv,na,(sv,t,av))->
              Result.Ok (nv,na,(sv,Lam nextVarIndex ty t,av))
            err ->
              err
    AppPT term1 term2 ->
      let
        r1 = transformTIter term1 allVars scopeVars nextVarIndex (nextAppIndex+1)
        r2 = andThenIter r1 term2
      in
      case r2 of
        Result.Ok (nv,na,(sv,t2,av)) ->
          Result.Ok (nv,na,(sv,App nextAppIndex (getT r1) (t2),av))
        err ->
          err
    CondPT  term1 term2 term3 ->
      let
        r1 = transformTIter term1 allVars scopeVars nextVarIndex nextAppIndex
        r2 = andThenIter r1 term2
        r3 = andThenIter r2 term3
      in
      case r3 of
        Result.Ok (nv,na,(sv,t3,av)) ->
          Result.Ok (nv,na,(sv,Cond (getT r1) (getT r2) (t3),av))
        err ->
          err
    IntPT val ->
      Result.Ok (nextVarIndex,nextAppIndex,(scopeVars,Int val,allVars))
    BoolPT val ->
      Result.Ok (nextVarIndex,nextAppIndex,(scopeVars,Bool val,allVars))



