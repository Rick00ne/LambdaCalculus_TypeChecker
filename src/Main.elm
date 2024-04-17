port module Main exposing (..)


import Browser
import Html exposing (Html, button, div, text, table, tr, td, textarea, span, input, label, form, h1, h2, a, br, p)
import Html.Events exposing (onClick, onInput, onCheck)
import Html.Attributes exposing (id, colspan, rowspan, style, placeholder, value, size, disabled, class, spellcheck, type_, checked, method, name, action, href, target, readonly, rows, cols)
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

-- PORTS

port reformat : () -> Cmd msg

-- MODEL


type alias Model =
  { tree:Tree
  , tNote:String
  , input: String
  , iNote:String
  , showTreeUI:Bool
  , steps: List Step
  , stepIndex: Int
  , vars: List String
  , typeVars: List (Int,Type)
  , displayRules: Bool
  , shortContext: Bool
  , contextSubs: List (Int,Context)
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
  | Nat Int
  | Bool Bool

type alias Step = {tree: Tree, subs: List (Int,Type), conSubs: List (Int,Context)}




init :() -> (Model, Cmd Msg)
init _ =
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
    , contextSubs = []
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
        Nat _->
          if ty==(TFree "Nat")
            then (Leaf,[],"NAT")
            else (TypeErr ("Found 'Int' constant but expected type '"++showType False ty++"'"),[],"NAT Err")
        Bool _->
          if ty==(TFree "Bool")
            then (Leaf,[],"BOOL")
            else (TypeErr ("Found 'Bool' constant but expected type '"++showType False ty++"'"),[],"BOOL Err")
        Var n  ->
          case (lookUp n c) of
            Just temp ->
              let
                found = (\(HasType x)->x) temp
                (good,subs)= typeCompare ty found
              in
              if good 
                then ((LeafC n ty c),subs,"VAR")
                else (TypeErr ("Found '"++showType False found++"' but expected type '"++showType False ty++"'"),subs,"VAR Err")
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
              (TypeErr ("Expected nonfunctional type '"++showType False ty++"' but found functional type (lambda abstraction)"),[],"ABS Err")
        _ ->
          (TypeErr "No rule found",[],"Err")
        
    _ ->
      (TypeErr "The term needs to be an annotation",[],"Err")

expandStepped : Tree -> List (Int,Type) -> List(Int,Context) -> List Step
expandStepped (Tree tree) passedTypeVars passedConSubs=
  let
    substitutedP = ((\(Tree t) -> t) (typeSub (Tree tree) passedTypeVars)).parent
    (assums,assTypeVars,rule)= makeAssumptions substitutedP
    allTypeVars = passedTypeVars++assTypeVars  --known type var substitutions (passed and from assumptions/rule)
    childConSubs =
      if ((first substitutedP)==[]) then passedConSubs
      else case (getIndex (first substitutedP) passedConSubs) of
        Nothing -> enrichedConSubs
        _ -> passedConSubs
    enrichedConSubs = passedConSubs++[(length passedConSubs, first substitutedP)]

  in
  case assums of
    TypeErr str ->
      [{tree= Tree {parent=tree.parent , children=TypeErr str, ruleName=rule}, subs= allTypeVars,conSubs=passedConSubs}]
    (Node list) ->
      let
        gradualEx = foldl                     --making sure every child knows about it's left (sooner stepped trough) sibling's type vars and context subs
          (\child accum -> case reverse accum of
            [] -> [expandStepped child allTypeVars childConSubs]
            c::_ -> case reverse c of
              [] ->
                [expandStepped child allTypeVars childConSubs]
              recent::_ ->
                accum ++ [expandStepped child recent.subs recent.conSubs]
          ) 
          []
          list
        chLastStepTrees = map                 --fully expanded subtrees of the children
          (\steps ->
            case reverse steps of
              [] ->
                Tree  { parent=([],Nat (-1))
                      , children=TypeErr "Internal Error! (please report this to feedback, if you get this error)"
                      , ruleName=""}
              last::_ ->
                last.tree
          )
          gradualEx
        childrenSteps = List.map2             --making sure every child has it's left (sooner stepped trough) sibling's fully expanded subtree
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
        laterSteps = concat childrenSteps     --steps per child into one list of steps
        baseStep = {tree= Tree {parent=tree.parent, children=Node list, ruleName=rule}, subs= allTypeVars, conSubs=childConSubs}
      in
      baseStep::laterSteps
    someLeaf ->
      [{tree= Tree {parent=tree.parent, children=someLeaf, ruleName=rule}, subs= allTypeVars, conSubs=passedConSubs}]

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
        tempT = {t | parent= (first t.parent,Ann t1 (tySub ty))}
      in
      case t.children of
        Node ch ->
          Tree { tempT | children = Node (map (\x-> typeSub x subs) ch)}
        LeafC n ty2 c ->
          Tree { tempT | children = LeafC n (tySub ty2) c}
        _ -> Tree tempT
    _ -> Tree t
    
typeCompare : Type -> Type -> (Bool,List (Int,Type))
typeCompare expected found=
  case expected of
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
    defStep = {tree= Tree {parent=([],Bool False) ,children=Node [],ruleName=""}, subs= [], conSubs=[]}
    getStep n = Maybe.withDefault (defStep) (selectStep n model.steps)
  in
  case msg of
    Reset ->
      let
        step = getStep 1
        t  = step.tree
        s  = step.subs
        cs = step.conSubs
      in
      ({model | tree=t,typeVars=s,stepIndex=1,contextSubs=cs},reformat ())
    StepForward ->
      let
        allowed = model.stepIndex < (length model.steps)
        i = model.stepIndex+1
        step = getStep i
        t  = step.tree
        s  = step.subs
        cs = step.conSubs
      in
      if allowed
        then ({model | tree=t,typeVars=s,stepIndex=i,contextSubs=cs},reformat ())
        else (model,Cmd.none)
    StepBack ->
      let
        allowed = model.stepIndex > 1
        i = model.stepIndex-1
        step = getStep i
        t  = step.tree
        s  = step.subs
        cs = step.conSubs
      in
      if allowed
        then ({model | tree=t,typeVars=s,stepIndex=i,contextSubs=cs},reformat ())
        else (model,Cmd.none)
    ExpandWhole ->
      let
        i = length model.steps
        step = getStep i
        t  = step.tree
        s  = step.subs
        cs = step.conSubs
      in
      ({model | tree=t,typeVars=s,stepIndex=i,contextSubs=cs},reformat ())
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
        newSteps r = 
          let
            steps = expandStepped (firstStep r).tree [] []
            laststep =
              case (take 1 (reverse steps)) of
                []     -> []
                step::_ ->
                  let
                    newTree = (typeSub step.tree step.subs)
                  in
                  if (newTree == step.tree) then
                    []
                  else
                    [ { step | 
                          tree = newTree,
                          subs = [] 
                      }
                    ]
          in
          Debug.log
            "steps"
            (((firstStep r)::steps)++laststep)
        firstStep r = {tree=Tree{parent=r,children=Node [],ruleName=""},subs=[],conSubs=[]}
      in
      case processedInput of
        Ok (root,vars) ->
          ({model | typeVars= [],
                    tree = (firstStep root).tree,
                    iNote= "",
                    showTreeUI= True,
                    steps= newSteps root,
                    stepIndex= 1,
                    vars= vars,
                    contextSubs = []
           }
          ,reformat ()
          )
        Err str ->
          ({model | iNote=str,
                    showTreeUI=False,
                    tNote=""
           }
          ,Cmd.none
          )
    SetShortContext b ->
      ({model | shortContext = b},reformat ())
    SetDisplayRules b ->
      ({model | displayRules = b},reformat ())

selectStep : Int -> List Step -> Maybe Step
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
    conSubsVisible= model.showTreeUI && model.contextSubs/=[] && model.shortContext
    stepCount = (fromInt model.stepIndex) ++ "/" ++ (fromInt (length model.steps))
  in
  div [ class "page" ]                                --Page 
      [ div
          [ id "report_overlay" ]
          [ div [ class "overlay_background"] []
          , div [ class "overlay_window"]
                [ h1    []
                        [ text "Report a bug"]
                , form  [ id "report_form"
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
          [ id "export_overlay" ]
          [ div [ class "overlay_background"] []
          , div [ class "overlay_window"]
                [ h1  []
                      [ text "Latex export" ]
                , div 
                    []
                    [ div []
                          [ text "Requires packages: amsmath, " 
                          , a [ href "https://research.nii.ac.jp/~tatsuta/proof-sty.html"
                              , target "_blank"
                              ]
                              [ text "proof" ]
                          , text ". Use this command:"
                          ]
                    , textarea [ class "latex", rows 1, readonly True, cols 100 ]
                          [ text "\\usepackage{proof,amsmath}" ]
                    , div []
                          [ text "Current step in latex format:" ]
                    , div [ id "unindented" ] 
                          [ text "$$"
                          , br [][] 
                          , showLatex 
                              model.tree
                              model.vars
                              model.displayRules
                              (if model.shortContext
                                then
                                  Just ([],0)
                                else
                                  Nothing
                              )
                          , br [][]
                          , text "$$"
                          ]
                    , textarea [ class "latex", id "latex_tree", readonly True, cols 100 ] []
                    ]
                ]
          ]
      , div
          [ id "help_overlay"]
          [ div [ class "overlay_background" ][]
          , div [ class "overlay_window" ]
                [ h1  []
                      [ text "How to use" ]
                , div
                    []
                    [ h2  []
                          [ text "What is this?" ]
                    , p   []
                          [ text 
                              """
                              Visualization tool for simply typed λ
                              calculus type derivation trees.
                              """
                          ]
                    , h2  []
                          [ text "Why?" ]
                    , p   []
                          [ text 
                              """
                              Because \"LAMBDA: Leading Advancements in Molecular
                              Biochemistry and Dimensional Astrophysics.\" - Black Mesa
                              """
                          ]
                    , h2  []
                          [ text "How?" ]
                    , p   []
                          [ text "Enter your λ calculus program into the input field."]
                    , p   []
                          [ text "Shortcuts:"
                          , br [][]
                          , text "\\l : λ"
                          , br [][]
                          , text "-> : →"
                          , br [][]
                          , text "|- : ⊢"
                          ]
                    , p   []
                          [ text 
                              """
                              Then you can proceed to the type derivation tree section
                              where you can walk trough the construction of the tree.
                              You can export the shown tree to LaTeX from here as well.
                              """
                          ]
                    , p   []
                          [ text
                              """
                              On the bottom part of the page there are sections for any
                              created type variables and context substitutions for the
                              currently selected step of the derivation tree.
                              """
                          ]
                    , h2  []
                          [ text "Syntax"]
                    , p   []
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
          , div []
                [ button [ id "help_button"] [] ]
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
          , div ([ class "control" ]
                ++if dui then [class "off"] else []
                )
                [ div []
                      [ button [disabled dui, id "export_button" ]
                               [text "LaTeX"]
                      ] 
                ]
          , div [] [ text model.tNote ]               --Note
          , div [ class "values" ]
                [ div [ class "vals_container" ]                 --Values of type variables
                      [ div [] [ text "Type variables:" ]
                      , if (typeVarsVisible)
                          then
                            div []
                                (showTypeVars model.typeVars)
                          else
                            div [ class "off" ][]
                      ]
                , div [ class "vals_container" ]                 --Values of context substitutions
                      [ div [] [ text "Context substitutions:" ]
                      , if (conSubsVisible)
                          then
                            div []
                                (showConSubs model.contextSubs model.vars)
                          else
                            div [ class "off" ][]
                      ]
                ]
                
          ]
      ]

showTree : Tree -> List String-> Bool -> Maybe (List (Int,Context),Int) -> Html Msg
showTree (Tree t) vars displayRules contextSubs =
  first (showTree_Next False (Tree t) vars displayRules contextSubs)

showLatex : Tree -> List String-> Bool -> Maybe (List (Int,Context),Int) -> Html Msg
showLatex (Tree t) vars displayRules contextSubs =
  first (showTree_Next True (Tree t) vars displayRules contextSubs)


showTree_Next : Bool -> Tree -> List String-> Bool -> Maybe (List (Int,Context),Int) -> (Html Msg,Int)
showTree_Next isLatex (Tree t) vars displayRules contextSubs =
  let
    ws = if isLatex
      then
        span [] [ br [][], text "&", br[][] ]
      else
        case (withDefault [] (Html.Parser.run "<td> &emsp; </td>") |> Html.Parser.Util.toVirtualDom) of
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
        (c,s)= showContext isLatex (first t.parent) vars contextSubs
      in
      pair
        (if isLatex then
          text ("\\text{"++c ++" $\\vdash$ "++ (showTerm True (second t.parent) vars) ++"}")
         else
          text (c ++" ⊢ "++ showTerm False (second t.parent) vars)
        )
        (getNext s)
    _ ->
      let
        (context,newSubs)=showContext isLatex (first t.parent) vars contextSubs
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
              b++[showTree_Next isLatex a vars displayRules s]
            )
            []
            ch
      in
      pair
        ((if isLatex then
           toLatex (if displayRules then t.ruleName else "")
          else
           table[]
         )
          [ (if isLatex then span [] else tr []) 
                  ((case (t.children) of
                    LeafC var ty c ->
                      if isLatex then
                        [text ( "\\text{"++ showTerm True (Var var) vars ++ ":" ++ showType True ty ++ " $\\in$ " ++ first (showContext True c vars newSubs)++"}")]
                      else
                        [td [] [text ( showTerm False (Var var) vars ++ ":" ++ showType False ty ++ " ∈ " ++ first (showContext False c vars newSubs))]]
                    Node children ->
                      intersperse
                        ws
                        (map
                          (if isLatex then \(x,_)-> x else \(x,_)->td [] [x])
                          (childrenFold children)
                        )
                    TypeErr str ->
                      if isLatex then
                        [text ("\\text{"++str++"}")]
                      else
                        [ span [] [text str] ]
                    _ -> if isLatex then [] else [ws]
                  )++if displayRules && not isLatex then
                       [td [rowspan 2, class "rule"][text ("("++t.ruleName++")")]]
                     else []
                  )
          , (if isLatex then
                  text (context ++" $\\vdash$ "++ showTerm True (second t.parent) vars)
            else
              tr []
                 [ td (case (t.children) of  
                     Node children -> [colspan ((length children)*2-1)]
                     _ -> []
                   )
                   [text (context ++" ⊢ "++ showTerm False (second t.parent) vars)]
                 ]
            )
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

toLatex : String -> List (Html Msg) -> Html Msg
toLatex rule children =
  span  []
        (
          case children of
            premisses::conclusion::_->
              [ text "\\infer" ]
              ++
              ( if rule=="" then [] else [text ("[^\\text{("++rule++")}]")] )
              ++
              [ br [][], text "{\\text{" ]
              ++
              [ conclusion ]
              ++
              [ text "}}", br [][], text "{" ]
              ++
              [ premisses ]
              ++
              [ br[][], text "}" ]
            _-> 
              [ text "LaTeX conversion error" ]
        )



showTerm : Bool -> Term -> List String -> String
showTerm isLatex t v =
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
      (showTerm isLatex term v)++":"++(showType isLatex ty)
    Var n ->
      case (atIndex n v) of
        Just str -> str
        Nothing  -> "var"++(fromInt n)
    Lam n ty term ->
      let
        lambda = if isLatex then "$\\lambda$" else "λ"
      in
      lambda++showTerm isLatex (Var n) v++":"++(showType isLatex ty)++"."++(showTerm isLatex term v)
    App _ t1 t2 ->
      (
        if isOpenEnded t1
        then
          "("++(showTerm isLatex t1 v)++")"
        else
          (showTerm isLatex t1 v)
      )
      ++
      (
        if priority t2 >= 2
        then
          " ("++(showTerm isLatex t2 v)++")"
        else
          " "++(showTerm isLatex t2 v)
      )
    Cond c t1 t2 ->
      "if "++showTerm isLatex c v++" then "++showTerm isLatex t1 v++" else "++showTerm isLatex t2 v
    Nat n -> fromInt n
    Bool b-> case b of 
      True -> "true"
      False -> "false"

showType : Bool -> Type -> String
showType isLatex t =
  case t of
    TFree str ->
      str
    Fun t1 t2 ->
      let
        arrow = if isLatex then "$\\to$" else "→"
      in
      case t1 of
        Fun _ _ ->
          "("++(showType isLatex t1)++")"++arrow++(showType isLatex t2)
        _ ->
          (showType isLatex t1)++arrow++(showType isLatex t2)
    TInf n  ->
      if isLatex then
        ("T$_"++fromInt n++"$")
      else
        ("T"++toSubscript n)

showContext : Bool -> Context -> List String -> Maybe (List (Int,Context),Int) -> (String,Maybe (List (Int,Context),Int))
showContext isLatex c v cs =
  let
    toStr n =
      case (atIndex n v) of
        Just str -> str
        Nothing  -> "var"++(fromInt n)
    showNormal con =
      (case con of
          [] -> ""
          (n,HasType t)::[]-> (toStr n)++":"++(showType isLatex t)
          (n,HasType t)::l -> (toStr n)++":"++(showType isLatex t)++", "++(showNormal l)
      )

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
                (l,r) =  shiftR context out
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
        gamma n = if isLatex then ("$\\Gamma_"++fromInt n++"$") else ("Γ"++toSubscript n)
      in
      pair 
        (
          if sub == -1
            then
              showNormal leftout
          else
            gamma sub++
            (if anyLeft then ", "++(showNormal leftout) else "")
        )
        newCs


showTypeVars : List (Int,Type) -> List (Html Msg)
showTypeVars vars =
  map (\(n,t) ->
        div [] [text ( (showType False (TInf n))++" = "++(showType False t) )] 
      )
      (List.sortBy (\(n,_)->n) vars)

showConSubs : List (Int,Context) -> List String -> List (Html Msg)
showConSubs conSubs v =
  map (\(n,c) ->
        let
          cs = Just (take n conSubs,0)
        in
        div [] [text ( "Γ"++(toSubscript n)++" = "++(first (showContext False c v cs)))] 
      )
      conSubs



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

toSubscript : Int -> String
toSubscript n =
      let
        delta = (Char.toCode '₀')-(Char.toCode '0')
      in
      String.fromList
        (map (\x -> Char.fromCode ((Char.toCode x) + delta)) (String.toList (fromInt n)))

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
  Parser.succeed (\c te ty -> (c,te,ty)) 
    |= contextP 
    |. Parser.spaces
    |. Parser.symbol "⊢"
    |. Parser.spaces
    |= termP
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
  Parser.succeed pair
    |= varP
    |. Parser.spaces
    |. Parser.symbol ":"
    |. Parser.spaces
    |= typeP

varP : Parser String
varP =
  Parser.variable
    { start = Char.isLower
    , inner = \c -> Char.isAlphaNum c
    , reserved = Set.fromList ["λ","if","then","else","true","false"]
    }

typeP : Parser Type
typeP =
  Pratt.expression
    { oneOf = 
      [ Pratt.literal (Parser.succeed TFree |= freeType)
      , brcType
      ]
    , andThenOneOf = [ Pratt.infixRight 10 (Parser.symbol "→") (Fun) ]
    , spaces = Parser.spaces}

freeType : Parser String
freeType =
  Parser.variable
    { start = Char.isUpper
    , inner = Char.isAlphaNum
    , reserved = Set.empty
    }

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
  Parser.succeed identity
    |. Parser.symbol "("
    |= Pratt.subExpression 0 config
    |. Parser.symbol ")"

condTerm : Pratt.Config ParsedTerm -> Parser ParsedTerm
condTerm config =
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
    getT r = (\(_,_,(_,t,_))->t) (withDefault (0,0,([],Nat 404,[])) r)
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
      Result.Ok (nextVarIndex,nextAppIndex,(scopeVars,Nat val,allVars))
    BoolPT val ->
      Result.Ok (nextVarIndex,nextAppIndex,(scopeVars,Bool val,allVars))



