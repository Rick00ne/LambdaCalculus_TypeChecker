<?php
	$errors = [];
	$errorMessage = '';
	if (!empty($_POST)) {
	   $message = $_POST['message'];

	   if (empty($message)) {
	       $errors[] = 'Message is empty';
	   }

	   if (empty($errors)) {
	   	   $host = 'lambdatypecheck-server.mysql.database.azure.com';
		   $username = $_ENV["DB_ADMIN"];
		   $password = $_ENV["DB_PASS"];
	       $db_name  = 'lambdatypecheck-database';

		   //Establishes the connection
		   $conn = mysqli_init();
		   mysqli_real_connect(
		   	$conn, $host, $username,
		   	$password, $db_name, 3306
		   );
	       if (mysqli_connect_errno()) {
             //header("HTTP/1.0 500 Internal Server Error");
	       	 echo json_encode(
              ['message'=>'Connection refused: '.mysqli_connect_error()]
             );
	       }
	       else {
	       	   $message  = mysqli_real_escape_string($conn,$message);
		       if (mysqli_query($conn, 
		       	"INSERT INTO Reports(Message) VALUES ('".$message ."');"
			   )) {
		       	echo json_encode(
               	    ['message'=>'Thank you for your feedback!']
                );
		       }
		       else {
				//header("HTTP/1.0 500 Internal Server Error");
				echo json_encode(
                 ['message'=>'query failed']
                );
			   }
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