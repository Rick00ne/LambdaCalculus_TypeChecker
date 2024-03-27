<?php
	$errors = [];
	$errorMessage = '';
	if (!empty($_POST)) {
	   $message = $_POST['message'];

	   if (empty($message)) {
	       $errors[] = 'Message is empty';
	   }

	   if (empty($errors)) {
	       if (true) {
             echo json_encode(['Message'=>'Thank you for your feedback!']);
	       }
	       else {
	         header("HTTP/1.0 500 Internal Server Error");
                   echo error_get_last();
	       }

	   } else {
	       header("HTTP/1.0 400 Bad Request");
	       $allErrors = join('', $errors);
	       echo $allErrors;
	   }
	}
	else {
	    header("HTTP/1.0 405 Method Not Allowed");
	}
?>