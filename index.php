


<html>
<head>
  <meta charset="UTF-8">
  <title>λ-Calculus TypeChecker</title>
  <script src="main.js"></script>
  <style>
    :root{
      color-scheme: dark;
      color:light-dark(black,black);
    }
  	body {
  		margin: 0;
  		padding: 0;
  	}
  	.page {
      position: relative;
  		min-height: 100vh;
  		min-width: fit-content;
  		display: flex;
  		flex-direction: column;
  		font-family: monospace;
      font-size: 30px;
  	}
  	.page ::-webkit-scrollbar{
  		width: 15px;
  		height: 15px;
  	}
  	#report_overlay, #export_overlay,
    #help_overlay, #unindented {
	  	display: none;
  	}
  	.overlay_background {
      z-index: 1;
  		position: fixed;
  		width: 100%;
  		height: 100%;
  		top:0;
  		left:0;
  		background-color: rgba(0,0,0,0.9);
  	}
    .overlay_window {
      z-index: 1;
      border: solid light-dark(rgb(102, 56, 0),darkorange) 2px;
      border-radius: 5px; 
      display: flex;
      flex-direction: column;
      background: light-dark(rgba(200,200,200,1),rgba(55,55,55,1));
      width: max-content;
      max-width: 75%;
      max-height: 80vh;
      min-height: 40%;
      padding: 1em;
      position: absolute;
      top: 50%;
      left: 50%;
      transform: translate(-50%,-50%);
      box-shadow: inset black 0 0 1em;
    }
    .overlay_window h1 {
      color: light-dark(rgb(102, 56, 0),darkorange);
      margin-top: 0;
    }
    .overlay_window > div {
      padding: 0.5em;
      overflow-y: auto;
      border: solid 2px black;
      background: darkgray;
      box-shadow: inset black 0 0 1em;
    }
    .overlay_window> div::-webkit-scrollbar-track {
      background: gray;
      box-shadow: inset black 0 0 10px;
    }
    .overlay_window> div::-webkit-scrollbar-thumb {
      background: light-dark(silver,black);
    }
    #help_overlay .overlay_window>div>div{ /*Rules list*/
      display: flex;
      flex-wrap: wrap;
    }
    #help_overlay table{
      padding: 1em;
    }
    .latex, form textarea{
      display: block;
      resize: none;
      font-size: inherit;
      color:inherit;
      text-wrap: nowrap;
      overflow: auto;
      margin: 0.2em auto;
      border: inset black 2px;
      padding: 5pt;
      background: white;
      width: 90%;
      max-height: 45vh;
      min-height: 10em;
    }
    .latex.oneline{
      max-height: none;
      min-height: auto;
    }
    .latex::-webkit-scrollbar-thumb,
    form textarea::-webkit-scrollbar-thumb {
      background: light-dark(silver,black);
    }
    form textarea{
      overflow: auto;
    }
    input[type="submit"]{
      display: block;
      border: 0.1em solid light-dark(rgb(102, 56, 0),darkorange);
      border-radius: 0.2em;
      font-size: inherit;
      color: light-dark(rgb(102, 56, 0),darkorange);
      background: light-dark(rgba(255,255,255,0.2),rgba(0,0,0,0.2));
      margin:auto;
    }
  	.header {
  		font-family: Arial;
  		text-align: center;
  		background: 
  			linear-gradient(
	  			180deg,
	  			light-dark(rgba(255, 198, 128,1),rgba(182,100,0,1)) 0%,
	  			light-dark(rgba(200,200,200,1),rgba(0,0,0,1)) 30%,
	  			light-dark(rgba(200,200,200,1),rgba(0,0,0,1)) 60%,
  				light-dark(rgba(160,160,160,1),rgba(33,33,33,1)) 100%
  			);
  		color: light-dark(rgb(102, 56, 0),darkorange);
  		display: grid;
    	grid-template-columns: 1fr auto 1fr;
    	align-items: end;
  	}
  	#report_button {
  		background: orange url(bug.svg);
    	background-size: 30px;
    	width: 34px;
    	height: 34px;
    	border: solid 2px light-dark(rgb(102, 56, 0),darkorange);
  	}
  	#report_button:hover {
  		background-color: darkorange;
  		border-color: orange;
  	}
    #help_button {
      background: orange url(help.svg);
      background-size: 30px;
      width: 34px;
      height: 34px;
      border: solid 2px light-dark(rgb(102, 56, 0),darkorange);
    }
    #help_button:hover {
      background-color: darkorange;
      border-color: orange;
    }
    #theme_button {
      background: orange url(theme.svg);
      background-size: 30px;
      width: 34px;
      height: 34px;
      border: solid 2px light-dark(rgb(102, 56, 0),darkorange);
      margin-right: 0.2em;
    }
    #theme_button:hover {
      background-color: darkorange;
      border-color: orange;
    }
  	.title {
  		width: max-content;
  		margin: auto;
  		padding: 40pt 20pt 20pt;
  		font-size: 42px;
  	}
  	.title span {
  		display:inline-block;
  		height: 1em;
  		line-height: 1em;
  	}
  	.logo {
  		width: 1em;
  		outline: light-dark(rgb(102, 56, 0),darkorange) solid 0.1em;
  		border-radius: 50%;
  		margin-right: 0.2em;
  	}
  	.header div:not(.title) {
  		padding: 0.2em
  	}
  	.header div:nth-child(1) {
  		justify-self:flex-start;
  	}
  	.header div:nth-child(3) {
  		justify-self:flex-end;
  	}
  	.app {
  		box-shadow: inset black 0 0 50pt;
  		background: light-dark(rgb(200,200,200),rgb(55,55,55));
  		flex: 1;
  		padding: 10pt;
  	}
  	.program_input {
  		min-width: max-content;
  		width: 80%;
  		margin: auto;
  		padding: 10pt;
  		display: flex;
  		align-items: flex-end; 
  	}
  	.program_input textarea {
  		resize: vertical;
  		font:inherit;
  		background: light-dark(peachpuff,rgb(211,134,41));
      color: inherit;
  		border: inset black 2px;
  		min-height: 4.5em;
  		height: 0;
  		overflow-x: hidden;
  		overflow-y: scroll;
      cursor:auto;
      width:100%;
  	}
  	.program_input textarea::-webkit-scrollbar-corner {
  		background: light-dark(peachpuff,rgb(211,134,41));
  	}
  	.program_input textarea::-webkit-scrollbar-thumb {
  		background-color: black;
  		border-radius: 0.25em
  	}
    .program_input>div{
      flex: 1;
    }
    .program_input>div>div{
      float:right;
      position: relative;
    }
    .program_input>div>div>button{ /*example selector*/
      float:right;
      border-radius: 0.2em 0.2em 0 0;
    }
  	.program_input>button {
  		margin-left: 0.5em;
  		width: 3em;
  	}
    .examples{
      display: flex;
      flex-direction: column;
      position:absolute;
      overflow: hidden;
      border: solid light-dark(rgb(102, 56, 0),darkorange) 0.1em;
      border-radius: 0.25em 0 0.25em 0.25em;
      width: max-content;
      top: 1.3em;
      right: 0;
    }
    .examples.hidden{
      display: none;
    }
    .examples button{
      border: none;
      border-radius: 0;
      background-color: light-dark(rgba(255, 255, 255,0.7),rgba(0,0,0,0.7));
    }
    .examples button:not(:last-child){
      border-bottom: solid 0.1em
    }
  	.parse_note {
  		overflow: hidden;
  	}
  	.parse_note>div {
  		overflow-y: scroll;
  		padding: 0.2em 0.5em;
  		background: lightPink;
  		outline: 0.1em solid maroon;
  		border-radius: 10pt;
  		width: 70%;
  		height: 4em;
  	}
  	.parse_note span {
  		font-family: Arial;
  		color: maroon;
  		font-weight: bold;
  	}
  	.err {
  		margin: 0.1em auto;
  		transition: margin 100ms ease-in-out;
  	}
  	.err::-webkit-scrollbar-thumb {
  		background-color: maroon;
  		border-radius: 0.25em
  	}
  	.err ::-webkit-scrollbar-track {
	  margin: 6px;
	}
  	.no_err {
  		margin: -5em auto 0;
  		transition: margin 100ms ease-in-out;
  	}
  	.zoom {
  		margin: 10pt auto 0;
  		width: max-content;
  		padding: 5pt;
  		border: solid light-dark(rgb(102, 56, 0),darkorange) 0.1em;
  		border-radius: 5pt 5pt 0 0;
  		border-bottom: none;
  		background: color-mix(in srgb,light-dark(rgb(194, 103, 0),orange), transparent 70%);
  		transition: 
  			border-color 200ms ease-in-out,
  			background   200ms ease-in-out;
  	}
  	.zoom div {
  		margin: auto;
  		width: max-content;
  	}
  	.zoom span {
  		display: inline-block;
  		width: 3em;
  		min-width: max-content;
  		text-align: center;
  	}
  	.zoom button {
  		width: 2em;
  		margin: 0.1em;
  	}
  	.tree {
  		resize: vertical;
  		min-height: 60px;
  		overflow: scroll;
  		margin: 0 auto;
  		border: inset black 2px;
  		height: 250pt;
  		padding: 5pt;
  		display: flex;
  		flex-direction: column-reverse;
  		align-items: center;
  		flex-wrap: wrap;
  		background: light-dark(peachpuff,rgb(211,134,41));
  		width: 80vw;
  		min-width: 1000px;
  		transition: 
  			background 200ms ease-in-out;
  	}
  	.tree>div {
  		width: max-content;
  	}
    #help_overlay table,
  	.tree table {
  		text-align: center;
  		border-spacing: 0px;
  		font-size: inherit;
  		display: inline-block;
  	}
    #help_overlay table>tr:nth-child(2)>td,
  	.tree>div div,.tree table>tr:nth-child(2)>td {
  		border-top: solid black 0.1em;
  	}
    #help_overlay table td:nth-child(2n):not(.rule),
  	.tree table>tr:nth-child(1)>td:nth-child(2n):not(.rule) {
  		width:2em;
  	}
    #help_overlay table .rule,
  	.tree .rule {
  		line-height:2em;
  		padding-left: 0.2em;
  	}
    #help_overlay tr,
  	.tree tr {
  		vertical-align: bottom;
  	}
    #help_overlay table *,
  	.tree * {
  		padding: 0;
  		line-height: 1em;
  	}
  	.tree span {
  		color: maroon;
  		font-weight: bold;
  	}
  	.tree.off {
  		background: light-dark(rgb(160, 160, 160),rgb(33,33,33));
  	}
  	.tree::-webkit-scrollbar-thumb {
  		background-color: orange;
  		border: solid light-dark(rgb(102, 56, 0),darkorange) 2px;
  		border-radius: 6px
  	}
  	.tree::-webkit-scrollbar-track {
  	  background: light-dark(rgb(160, 160, 160),rgb(33,33,33));
  	  border: inset black 2px;
  	}
  	.tree::-webkit-scrollbar-corner {
  		background: light-dark(rgb(160, 160, 160),rgb(33,33,33));
  	}
    .program_input textarea::-webkit-resizer,
  	.tree::-webkit-resizer {
  	    background: url(resizer.svg) no-repeat;
  	    background-size: 100%;
  	}
  	.control, .zoom {
  		color: light-dark(rgb(102, 56, 0),darkorange);
  	}
  	.control {
  		margin: 0 auto;
  		width: max-content;
  		padding: 5pt;
  		border: solid light-dark(rgb(102, 56, 0),darkorange) 0.1em;
  		border-radius: 0 0 5pt 5pt;
  		border-top: none;
  		background: color-mix(in srgb,light-dark(rgb(194, 103, 0),orange), transparent 70%);
  		transition: 
  			border-color 200ms ease-in-out,
  			background   200ms ease-in-out;
  	}
  	.control div {
  		margin: auto;
  		width: max-content;
  	}
  	.control span {
  		display: inline-block;
  		width: 3em;
  		min-width: max-content;
  		text-align: center;
  		font-weight: bold;
  	}
  	.control button {
  		width: 2em;
  		margin: 0.1em;
  		padding: 2px 6px; 
  	}
  	.control label {
  		margin: 0.1em;
  		border: 0.1em solid light-dark(rgb(102, 56, 0),darkorange);
	    border-radius: 0.2em;
	    font-size: inherit;
	    color: light-dark(rgb(102, 56, 0),darkorange);
	    background: light-dark(rgba(255, 255, 255,0.2),rgba(0,0,0,0.2));
	    padding: 2px 2px 2px 6px;
    	display: inline-grid;
    	width: 9em;
    	grid-auto-flow: column;
    	grid-template-columns: auto 1em;
    	justify-items: stretch;
    	align-items: stretch;
    	text-align: center;
    	user-select: none;
  	}
  	.control label input {
  		margin: 0;
    	appearance: none;
    	display: grid;
    	place-content: center;
    	font-size: inherit;
    	font-weight: bold;
    	line-height: 0;
    	color: inherit;
	    border-radius: 0.1em;
	    background: rgba(255,255,255,0.2);
  	}
  	.control label input:checked::before {
  		content: "✓";
  	}
  	.control label input::before {
  		content: "✗";
  	}
  	.control:not(.off) label input:not(:checked) {
  		color: maroon;
  	}
  	.control.off label {
  		border-color: light-dark(gray,darkgray);
	    color: light-dark(gray,darkgray);
	    background: rgba(255,255,255,0.2);
  	}
  	.control:not(.off) label:hover {
		  background: light-dark(rgba(255, 255, 255,0.8),rgba(0,0,0,0.9));
	  }
    #export_button{
      width: max-content;
    }
  	/*.control span ~ label {
  		grid-template-columns: 1em auto;
  	}*/
  	.vals_container > div:last-child {
      text-wrap: nowrap;
  		margin: auto;
  		border: 0.1em solid;
  		border-radius: 10pt;
  		padding: 10pt;
  		display: flex;
  		flex-flow: column wrap;
  		align-content: flex-start;
  		line-height: 1em;
  		height: 4.5em;
  		overflow-x: scroll;
  		border-color: light-dark(rgb(102, 56, 0),darkorange);
  		background: light-dark(rgba(194, 103, 0, 0.3),rgba(255,165,0,0.3));
  		transition: 
  			border-color 200ms ease-in-out,
  			background   200ms ease-in-out;
  	}
  	.vals_container > div:last-child::-webkit-scrollbar-thumb {
  		background-color: light-dark(rgb(194, 103, 0),orange);
  		border-radius: 0.25em
  	}
  	.vals_container > div:last-child > div {
  		margin-right: 0.5em;
  		padding-right: 0.5em;
  	}
  	.vals_container > div:last-child > div:nth-child(4n):not(:last-child) {
  		border-right: solid light-dark(rgb(102, 56, 0),darkorange) 0.1em;
  	}
  	.vals_container > div:last-child > div:nth-child(4n+3):not(:last-child):not(:nth-last-child(2)) {
  		border-right: solid light-dark(rgb(102, 56, 0),darkorange) 0.1em;
  	}
  	.vals_container > div:last-child > div:nth-child(4n+2):not(:last-child):not(:nth-last-child(2)):not(:nth-last-child(3)) {
  		border-right: solid light-dark(rgb(102, 56, 0),darkorange) 0.1em;
  	}
  	.vals_container > div:last-child > div:nth-child(4n+1):not(:last-child):not(:nth-last-child(2)):not(:nth-last-child(3)):not(:nth-last-child(4)) {
  		border-right: solid light-dark(rgb(102, 56, 0),darkorange) 0.1em;
  	}
  	.vals_container > div:first-child {
  		color: light-dark(black,white);
  		font-weight: bold;
  	}
  	.vals_container > div.off, .control.off, .zoom.off {
  		border-color: gray;
  		background: rgba(33,33,33,0.3);
  		color: light-dark(gray,darkgray);
  	}
    .vals_container{
      min-width: 15em;
      padding: 1em;
      width: 40vw;
    }
    .values {
      display: flex;
      justify-content: center;
    }
  	button {
	    border: 0.1em solid light-dark(rgb(102, 56, 0),darkorange);
	    border-radius: 0.2em;
	    font-size: inherit;
	    color: light-dark(rgb(102, 56, 0),darkorange);
	    background: light-dark(rgba(255, 255, 255,0.3),rgba(0,0,0,0.2));
  	}
  	button:hover, input[type="submit"]:hover {
  		background: light-dark(rgba(255, 255, 255,0.8),rgba(0,0,0,0.9));
  	}
  	button:active, input[type="submit"]:active {
  		background: light-dark(rgba(255, 255, 255,1),rgba(0,0,0,0.5));
  	}
  	button:disabled {
  	    border-color: light-dark(gray,darkgray);
  	    color: light-dark(gray,darkgray);
  	    background: rgba(255,255,255,0.2);
  	}

  </style>
</head>

<body>
  <div id="myapp"></div>
  <script>
	  var app = Elm.Main.init({
	    node: document.getElementById('myapp')
	  });

	  window.addEventListener('input', event => {
	    // capture the value the browser set
	    const target = event.target
	    const { value, selectionStart } = target
	    
	    // wait for Elm to decide what the new value
	    // of the input actually should look like
	    requestAnimationFrame(() => {
	        const newValue = target.value
	        if (value !== newValue) {
	            target.selectionEnd = target.selectionStart =
	                selectionStart - (value.length - newValue.length)
	        }
	    })      
	  }, true);

	  var treeDiv = document.getElementsByClassName("tree")[0]
	  var zoom = 30;
	  var minusButton = document.getElementById("zoom_minus");
	  var plusButton = document.getElementById("zoom_plus");
	  var reportOverlay = document.getElementById("report_overlay");
    var exportOverlay = document.getElementById("export_overlay");
    var helpOverlay = document.getElementById("help_overlay");
    var unindented = document.getElementById("unindented");
    var latexTree = document.getElementById("latex_tree");
    var root = document.querySelector(':root');

    app.ports.reformat.subscribe(function(){
      requestAnimationFrame(() => {
          reformat();
      }) 
    });

    function reformat(){
      const regex1 = /<[/]*span>/g;
      const regex2 = /&amp;/g;
      var lines =unindented.innerHTML.replace(regex1,"").replace(regex2,"&").split("<br>");
      var i = 0;
      var len = lines.length;
      var indent = 0;
      var arePremisses = false;
      while (i<len){
        var line = lines[i];
        if (line.startsWith('}')){
          lines[i]=(" ".repeat(indent-1))+lines[i];
          indent-=3;
        }
        else if (line.startsWith('&')){
          lines[i]=(" ".repeat(indent-1))+lines[i];
        }
        else{
          lines[i]=(" ".repeat(indent))+lines[i];
          if (arePremisses){
            arePremisses = false;
            indent++;
          }
          if (line.includes("\\infer")){
            indent += 2;
            i++;
            lines[i]=(" ".repeat(indent))+lines[i];
            arePremisses = true;
          }
        }
        i++;
      }
      latexTree.value = lines.join("\n");
      latexTree.rows = lines.length;
    }

	  plusButton.onclick = zoomIn;
	  minusButton.onclick = zoomOut;
	  document.getElementById("report_button").onclick = reportOverlayOn;
    document.getElementById("export_button").onclick = exportOverlayOn;
    document.getElementById("help_button").onclick = helpOverlayOn;
    document.getElementById("theme_button").onclick = switchTheme;
    const elems = document.getElementsByClassName("overlay_background");
    for (let i = 0; i < elems.length; i++) {
      elems[i].onclick = function()
        {this.parentElement.style.display = "none";}
    }

	  function refreshSize(){
	    treeDiv.style.fontSize=zoom+"px";
	    console.log("zoom: " + treeDiv.style.fontSize);
	    if (zoom<=10){
	    	minusButton.disabled=true;
	    }
	    else{
	    	minusButton.disabled=false;
	    }

	    if (zoom>=100){
	    	plusButton.disabled=true;
	    }
	    else{
	    	plusButton.disabled=false;
	    }
	  }

	  function zoomIn(){

	  	zoom+=5;
	  	refreshSize();
	  }

	  function zoomOut(){
	  	zoom-=5;
	  	refreshSize();
	  }

	  function reportOverlayOn(){
	  	reportOverlay.style.display = "block";
	  }

	  function reportOverlayOff(){
	  	reportOverlay.style.display = "none";
	  }

    function exportOverlayOn(){
      exportOverlay.style.display = "block";
    }

    function exportOverlayOff(){
      exportOverlay.style.display = "none";
    }

    function helpOverlayOn(){
      helpOverlay.style.display = "block";
    }

    function helpOverlayOff(){
      helpOverlay.style.display = "none";
    }

    function switchTheme(){
      if (getComputedStyle(root).getPropertyValue('color-scheme')=='dark'){
        root.style.setProperty('color-scheme', 'light')
      }
      else{
        root.style.setProperty('color-scheme', 'dark')
      }
    }
  </script>
  <script src="validate.min.js"></script>
  <script>


    const constraints = {
        message: {
            presence: { allowEmpty: false }
        }
    };

    const form = document.getElementById('report_form');
    form.addEventListener('submit', function (event) {
     	event.preventDefault();
        const formValues = {
            message: form.elements.message.value
        };

        const errors = validate(formValues, constraints);
        if (errors) {
            const errorMessage = Object
                .values(errors)
                .map(function (fieldValues) {
                    return fieldValues.join(', ')
                })
                .join("\n");

            alert(errorMessage);
        }
        else{
        	const req = new Request("report_form.php", {
			  method: 'POST',
			  body: new FormData(form)
			});

			fetch(req)
			  .then(response => {
			    if (!response.ok) {
			      throw new Error('Failed to submit bug report');
			    }
			    return response.text();
			  })
			  .then(data => {
			    // Handle success
			    reportOverlayOff();
			    alert(data.message);
                            console.log("success: ",data);
			  })
			  .catch(error => {
			    // Handle error
			    alert(error.message);
                            console.log("error: ",error);
			  });
        }
    }, false);
  </script>
</body>
</html>