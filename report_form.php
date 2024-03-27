<?php
	$errors = [];
	$errorMessage = '';
	if (!empty($_POST)) {
	   $message = $_POST['message'];

	   if (empty($message)) {
	       $errors[] = 'Message is empty';
	   }

	   if (empty($errors)) {
	       $email = 'NoReply@LamCalTypeCheck.com';
	       $toEmail = 'richard.jurko.2@student.tuke.sk';
	       $emailSubject = 'LamCalTypeCheck Bug Report';
	       $headers = ['From'=>$email, 'Content-type'=>'text/html; charset=utf-8'];
	       $bodyParagraphs = [ 'Report message:', $message];
	       $body = join(PHP_EOL, $bodyParagraphs);

	       if (mail($toEmail, $emailSubject, $body, $headers)) {
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