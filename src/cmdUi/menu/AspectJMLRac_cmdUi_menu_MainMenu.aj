import cmdUi.menu.*;
import org.jmlspecs.ajmlrac.runtime.*;
import org.jmlspecs.lang.annotation.*;
import java.time.Duration;
import cmdUi.Main;
import cmdUi.PilhaListView;
import controller.Controller;
import java.util.Map;


privileged aspect AspectJMLRac_cmdUi_menu_MainMenud1420e49_94b4_4e0c_abf8_c4a8d03fec01 {

 declare precedence: AspectJMLRac_*, *;







  /** Generated by AspectJML to check the normal postcondition of
   * method MainMenu. */
  after (final cmdUi.menu.MainMenu object$rac, final controller.Controller con, final int options) returning () :
     execution(cmdUi.menu.MainMenu.new( controller.Controller, int )) && this(object$rac) && args(con, options) {
       String nPostErrorMsg =  "";
       String evalErrorMsg = "";
       boolean rac$b = true;
         nPostErrorMsg =  "by method cmdUi.menu.MainMenu.<init> regarding specifications at \nFile \"cmdUi.menu.MainMenu.java\", line 14, character 30 (cmdUi.menu.MainMenu.java:14), and \nby method cmdUi.menu.MainMenu.<init> regarding code at \nFile \"cmdUi.menu.MainMenu.java\""+", when \n"+"\t\'this.parent\' is "+object$rac.parent;
         evalErrorMsg = "Invalid expression in \"cmdUi.menu.MainMenu.java\" by method cmdUi.menu.MainMenu.<init> regarding specifications at \nline 14, character 30 (cmdUi.menu.MainMenu.java:14)"+", when \n"+"\t\'this.parent\' is "+object$rac.parent+"\nCaused by: ";
       if (((con != null) && true)){
         try {
           rac$b = (object$rac.parent == null);
         } catch (JMLNonExecutableException rac$nonExec) {
            rac$b = false;
         } catch (Throwable rac$cause) {
            if(rac$cause instanceof JMLAssertionError) {
              throw (JMLAssertionError) rac$cause;
            }
            else {
              throw new JMLEvaluationError(evalErrorMsg + rac$cause);
            }
         }
        JMLChecker.checkNormalPostcondition(rac$b, nPostErrorMsg, -1, "cmdUi.menu.MainMenu.<init>(controller.Controller, int)");
       }

     }

  /** Generated by AspectJML to check the exceptional postcondition of
   * method MainMenu. */
  after (final cmdUi.menu.MainMenu object$rac, final controller.Controller con, final int options) throwing (Throwable rac$e) :
     execution(cmdUi.menu.MainMenu.new( controller.Controller, int )) && this(object$rac) && args(con, options) {
           JMLChecker.rethrowJMLAssertionError(rac$e, "cmdUi.menu.MainMenu.<init>(controller.Controller, int)");
           boolean rac$b = true;
           String rac$ErrorMsg = "";

  		   if (rac$b && ((con != null) && true)) {
  		     if (rac$e instanceof java.lang.RuntimeException) {
  			   java.lang.RuntimeException jml$ex = (java.lang.RuntimeException) rac$e;
  			   boolean rac$b0 = true;
  			   try{			     
  			     rac$b0 = true;
  			   }   catch (JMLNonExecutableException rac$nonExec) {
  			     throw new JMLEvaluationError("Invalid Expression in \"cmdUi.menu.MainMenu.java\" by method cmdUi.menu.MainMenu.<init>\nCaused by: "+rac$e);
  			   }
  			   if(!rac$b0) {
  			     if(rac$ErrorMsg.equals("")) {
  			       rac$ErrorMsg = "jml$ex";
  			     }
  			     else {
  			       rac$ErrorMsg += " and jml$ex";
  			     }
  			   }
  			   rac$b = rac$b && rac$b0;
           if(rac$ErrorMsg.indexOf("and") >= 0 ){
             rac$ErrorMsg += " are ";
           }
           else{
             rac$ErrorMsg += " is ";
           }
               JMLChecker.checkExceptionalPostcondition(rac$b,"by method cmdUi.menu.MainMenu.<init> regarding code at \nFile \"cmdUi.menu.MainMenu.java\""+"\n\t"+rac$ErrorMsg+rac$e, "jml$ex", true, -1, "cmdUi.menu.MainMenu.<init>(controller.Controller, int)", rac$e);
  		 }
  		   }
  	 }

  /** Generated by AspectJML to check the exceptional postcondition of
   * method draw. */
  after (final cmdUi.menu.MainMenu object$rac) throwing (Throwable rac$e) :
     (execution(void cmdUi.menu.MainMenu.draw())) && this(object$rac) {
           JMLChecker.rethrowJMLAssertionError(rac$e, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".draw()");
           boolean rac$b = true;
           String rac$ErrorMsg = "";

  		   if (true) {
  		     if (rac$e instanceof java.lang.RuntimeException) {
  			   java.lang.RuntimeException jml$ex = (java.lang.RuntimeException) rac$e;
  			   boolean rac$b0 = true;
  			   try{			     
  			     rac$b0 = true;
  			   }   catch (JMLNonExecutableException rac$nonExec) {
  			     throw new JMLEvaluationError("Invalid Expression in \"cmdUi.menu.MainMenu.java\" by method cmdUi.menu.MainMenu.draw\nCaused by: "+rac$e);
  			   }
  			   if(!rac$b0) {
  			     if(rac$ErrorMsg.equals("")) {
  			       rac$ErrorMsg = "jml$ex";
  			     }
  			     else {
  			       rac$ErrorMsg += " and jml$ex";
  			     }
  			   }
  			   rac$b = rac$b && rac$b0;
           if(rac$ErrorMsg.indexOf("and") >= 0 ){
             rac$ErrorMsg += " are ";
           }
           else{
             rac$ErrorMsg += " is ";
           }
               JMLChecker.checkExceptionalPostcondition(rac$b,"by method cmdUi.menu.MainMenu.draw regarding code at \nFile \"cmdUi.menu.MainMenu.java\""+"\n\t"+rac$ErrorMsg+rac$e, "jml$ex", true, -1, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".draw()", rac$e);
  		 }
  		   }
  	 }


  /** Generated by AspectJML to check the normal postcondition of
   * method processInput. */
  after (final cmdUi.menu.MainMenu object$rac, final int op) returning (final cmdUi.menu.AbstractMenu rac$result) :
     (execution(cmdUi.menu.AbstractMenu cmdUi.menu.MainMenu.processInput(int))) && this(object$rac) && args(op) {
       String nPostErrorMsg =  "";
       String evalErrorMsg = "";
       boolean rac$b = true;
         nPostErrorMsg =  "by method cmdUi.menu.MainMenu.processInput regarding code at \nFile \"cmdUi.menu.MainMenu.java\", line 53 (cmdUi.menu.MainMenu.java:53)";
         evalErrorMsg = "Invalid expression in \"cmdUi.menu.MainMenu.java\"\nCaused by: ";
       if (true){
         try {
           rac$b = (rac$result != null);
         } catch (JMLNonExecutableException rac$nonExec) {
            rac$b = false;
         } catch (Throwable rac$cause) {
            if(rac$cause instanceof JMLAssertionError) {
              throw (JMLAssertionError) rac$cause;
            }
            else {
              throw new JMLEvaluationError(evalErrorMsg + rac$cause);
            }
         }
        JMLChecker.checkNormalPostcondition(rac$b, nPostErrorMsg, -1, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".processInput(int)");
       }

     }

  /** Generated by AspectJML to check the exceptional postcondition of
   * method processInput. */
  after (final cmdUi.menu.MainMenu object$rac, final int op) throwing (Throwable rac$e) :
     (execution(cmdUi.menu.AbstractMenu cmdUi.menu.MainMenu.processInput(int))) && this(object$rac) && args(op) {
           JMLChecker.rethrowJMLAssertionError(rac$e, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".processInput(int)");
           boolean rac$b = true;
           String rac$ErrorMsg = "";

  		   if (true) {
  		     if (rac$e instanceof java.lang.RuntimeException) {
  			   java.lang.RuntimeException jml$ex = (java.lang.RuntimeException) rac$e;
  			   boolean rac$b0 = true;
  			   try{			     
  			     rac$b0 = true;
  			   }   catch (JMLNonExecutableException rac$nonExec) {
  			     throw new JMLEvaluationError("Invalid Expression in \"cmdUi.menu.MainMenu.java\" by method cmdUi.menu.MainMenu.processInput\nCaused by: "+rac$e);
  			   }
  			   if(!rac$b0) {
  			     if(rac$ErrorMsg.equals("")) {
  			       rac$ErrorMsg = "jml$ex";
  			     }
  			     else {
  			       rac$ErrorMsg += " and jml$ex";
  			     }
  			   }
  			   rac$b = rac$b && rac$b0;
           if(rac$ErrorMsg.indexOf("and") >= 0 ){
             rac$ErrorMsg += " are ";
           }
           else{
             rac$ErrorMsg += " is ";
           }
               JMLChecker.checkExceptionalPostcondition(rac$b,"by method cmdUi.menu.MainMenu.processInput regarding code at \nFile \"cmdUi.menu.MainMenu.java\", line 53 (cmdUi.menu.MainMenu.java:53)"+"\n\t"+rac$ErrorMsg+rac$e, "jml$ex", true, -1, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".processInput(int)", rac$e);
  		 }
  		   }
  	 }


  /** Generated by AspectJML to check the exceptional postcondition of
   * method opFinalizar. */
  after (final cmdUi.menu.MainMenu object$rac) throwing (Throwable rac$e) :
     (execution(void cmdUi.menu.MainMenu.opFinalizar())) && this(object$rac) {
           JMLChecker.rethrowJMLAssertionError(rac$e, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".opFinalizar()");
           boolean rac$b = true;
           String rac$ErrorMsg = "";

  		   if (true) {
  		     if (rac$e instanceof java.lang.RuntimeException) {
  			   java.lang.RuntimeException jml$ex = (java.lang.RuntimeException) rac$e;
  			   boolean rac$b0 = true;
  			   try{			     
  			     rac$b0 = true;
  			   }   catch (JMLNonExecutableException rac$nonExec) {
  			     throw new JMLEvaluationError("Invalid Expression in \"cmdUi.menu.MainMenu.java\" by method cmdUi.menu.MainMenu.opFinalizar\nCaused by: "+rac$e);
  			   }
  			   if(!rac$b0) {
  			     if(rac$ErrorMsg.equals("")) {
  			       rac$ErrorMsg = "jml$ex";
  			     }
  			     else {
  			       rac$ErrorMsg += " and jml$ex";
  			     }
  			   }
  			   rac$b = rac$b && rac$b0;
           if(rac$ErrorMsg.indexOf("and") >= 0 ){
             rac$ErrorMsg += " are ";
           }
           else{
             rac$ErrorMsg += " is ";
           }
               JMLChecker.checkExceptionalPostcondition(rac$b,"by method cmdUi.menu.MainMenu.opFinalizar regarding code at \nFile \"cmdUi.menu.MainMenu.java\""+"\n\t"+rac$ErrorMsg+rac$e, "jml$ex", true, -1, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".opFinalizar()", rac$e);
  		 }
  		   }
  	 }


  /** Generated by AspectJML to check the exceptional postcondition of
   * method opReiniciar. */
  after (final cmdUi.menu.MainMenu object$rac) throwing (Throwable rac$e) :
     (execution(void cmdUi.menu.MainMenu.opReiniciar())) && this(object$rac) {
           JMLChecker.rethrowJMLAssertionError(rac$e, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".opReiniciar()");
           boolean rac$b = true;
           String rac$ErrorMsg = "";

  		   if (true) {
  		     if (rac$e instanceof java.lang.RuntimeException) {
  			   java.lang.RuntimeException jml$ex = (java.lang.RuntimeException) rac$e;
  			   boolean rac$b0 = true;
  			   try{			     
  			     rac$b0 = true;
  			   }   catch (JMLNonExecutableException rac$nonExec) {
  			     throw new JMLEvaluationError("Invalid Expression in \"cmdUi.menu.MainMenu.java\" by method cmdUi.menu.MainMenu.opReiniciar\nCaused by: "+rac$e);
  			   }
  			   if(!rac$b0) {
  			     if(rac$ErrorMsg.equals("")) {
  			       rac$ErrorMsg = "jml$ex";
  			     }
  			     else {
  			       rac$ErrorMsg += " and jml$ex";
  			     }
  			   }
  			   rac$b = rac$b && rac$b0;
           if(rac$ErrorMsg.indexOf("and") >= 0 ){
             rac$ErrorMsg += " are ";
           }
           else{
             rac$ErrorMsg += " is ";
           }
               JMLChecker.checkExceptionalPostcondition(rac$b,"by method cmdUi.menu.MainMenu.opReiniciar regarding code at \nFile \"cmdUi.menu.MainMenu.java\""+"\n\t"+rac$ErrorMsg+rac$e, "jml$ex", true, -1, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".opReiniciar()", rac$e);
  		 }
  		   }
  	 }


  /** Generated by AspectJML to check the exceptional postcondition of
   * method opVirarCartaEstoque. */
  after (final cmdUi.menu.MainMenu object$rac) throwing (Throwable rac$e) :
     (execution(void cmdUi.menu.MainMenu.opVirarCartaEstoque())) && this(object$rac) {
           JMLChecker.rethrowJMLAssertionError(rac$e, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".opVirarCartaEstoque()");
           boolean rac$b = true;
           String rac$ErrorMsg = "";

  		   if (true) {
  		     if (rac$e instanceof java.lang.RuntimeException) {
  			   java.lang.RuntimeException jml$ex = (java.lang.RuntimeException) rac$e;
  			   boolean rac$b0 = true;
  			   try{			     
  			     rac$b0 = true;
  			   }   catch (JMLNonExecutableException rac$nonExec) {
  			     throw new JMLEvaluationError("Invalid Expression in \"cmdUi.menu.MainMenu.java\" by method cmdUi.menu.MainMenu.opVirarCartaEstoque\nCaused by: "+rac$e);
  			   }
  			   if(!rac$b0) {
  			     if(rac$ErrorMsg.equals("")) {
  			       rac$ErrorMsg = "jml$ex";
  			     }
  			     else {
  			       rac$ErrorMsg += " and jml$ex";
  			     }
  			   }
  			   rac$b = rac$b && rac$b0;
           if(rac$ErrorMsg.indexOf("and") >= 0 ){
             rac$ErrorMsg += " are ";
           }
           else{
             rac$ErrorMsg += " is ";
           }
               JMLChecker.checkExceptionalPostcondition(rac$b,"by method cmdUi.menu.MainMenu.opVirarCartaEstoque regarding code at \nFile \"cmdUi.menu.MainMenu.java\""+"\n\t"+rac$ErrorMsg+rac$e, "jml$ex", true, -1, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".opVirarCartaEstoque()", rac$e);
  		 }
  		   }
  	 }


  /** Generated by AspectJML to check the exceptional postcondition of
   * method opMoverCartas. */
  after (final cmdUi.menu.MainMenu object$rac) throwing (Throwable rac$e) :
     (execution(void cmdUi.menu.MainMenu.opMoverCartas())) && this(object$rac) {
           JMLChecker.rethrowJMLAssertionError(rac$e, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".opMoverCartas()");
           boolean rac$b = true;
           String rac$ErrorMsg = "";

  		   if (true) {
  		     if (rac$e instanceof java.lang.RuntimeException) {
  			   java.lang.RuntimeException jml$ex = (java.lang.RuntimeException) rac$e;
  			   boolean rac$b0 = true;
  			   try{			     
  			     rac$b0 = true;
  			   }   catch (JMLNonExecutableException rac$nonExec) {
  			     throw new JMLEvaluationError("Invalid Expression in \"cmdUi.menu.MainMenu.java\" by method cmdUi.menu.MainMenu.opMoverCartas\nCaused by: "+rac$e);
  			   }
  			   if(!rac$b0) {
  			     if(rac$ErrorMsg.equals("")) {
  			       rac$ErrorMsg = "jml$ex";
  			     }
  			     else {
  			       rac$ErrorMsg += " and jml$ex";
  			     }
  			   }
  			   rac$b = rac$b && rac$b0;
           if(rac$ErrorMsg.indexOf("and") >= 0 ){
             rac$ErrorMsg += " are ";
           }
           else{
             rac$ErrorMsg += " is ";
           }
               JMLChecker.checkExceptionalPostcondition(rac$b,"by method cmdUi.menu.MainMenu.opMoverCartas regarding code at \nFile \"cmdUi.menu.MainMenu.java\""+"\n\t"+rac$ErrorMsg+rac$e, "jml$ex", true, -1, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".opMoverCartas()", rac$e);
  		 }
  		   }
  	 }


  /** Generated by AspectJML to check the normal postcondition of
   * method setPilhaListView. */
  after (final cmdUi.menu.MainMenu object$rac, final cmdUi.PilhaListView plv) returning () :
     (execution(void cmdUi.menu.MainMenu.setPilhaListView(cmdUi.PilhaListView))) && this(object$rac) && args(plv) {
       String nPostErrorMsg =  "";
       String evalErrorMsg = "";
       boolean rac$b = true;
         nPostErrorMsg =  "by method cmdUi.menu.MainMenu.setPilhaListView regarding specifications at \nFile \"cmdUi.menu.MainMenu.java\", line 89, character 39 (cmdUi.menu.MainMenu.java:89), and \nby method cmdUi.menu.MainMenu.setPilhaListView regarding code at \nFile \"cmdUi.menu.MainMenu.java\""+", when \n"+"\t\'plv\' is "+plv;
         evalErrorMsg = "Invalid expression in \"cmdUi.menu.MainMenu.java\" by method cmdUi.menu.MainMenu.setPilhaListView regarding specifications at \nline 89, character 39 (cmdUi.menu.MainMenu.java:89)"+", when \n"+"\t\'plv\' is "+plv+"\nCaused by: ";
       if (((plv != null) && (plv != null))){
         try {
           rac$b = (object$rac.plv == plv);
         } catch (JMLNonExecutableException rac$nonExec) {
            rac$b = false;
         } catch (Throwable rac$cause) {
            if(rac$cause instanceof JMLAssertionError) {
              throw (JMLAssertionError) rac$cause;
            }
            else {
              throw new JMLEvaluationError(evalErrorMsg + rac$cause);
            }
         }
        JMLChecker.checkNormalPostcondition(rac$b, nPostErrorMsg, -1, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".setPilhaListView(cmdUi.PilhaListView)");
       }

     }

  /** Generated by AspectJML to check the exceptional postcondition of
   * method setPilhaListView. */
  after (final cmdUi.menu.MainMenu object$rac, final cmdUi.PilhaListView plv) throwing (Throwable rac$e) :
     (execution(void cmdUi.menu.MainMenu.setPilhaListView(cmdUi.PilhaListView))) && this(object$rac) && args(plv) {
           JMLChecker.rethrowJMLAssertionError(rac$e, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".setPilhaListView(cmdUi.PilhaListView)");
           boolean rac$b = true;
           String rac$ErrorMsg = "";

  		   if (rac$b && ((plv != null) && (plv != null))) {
  		     if (rac$e instanceof java.lang.RuntimeException) {
  			   java.lang.RuntimeException jml$ex = (java.lang.RuntimeException) rac$e;
  			   boolean rac$b0 = true;
  			   try{			     
  			     rac$b0 = true;
  			   }   catch (JMLNonExecutableException rac$nonExec) {
  			     throw new JMLEvaluationError("Invalid Expression in \"cmdUi.menu.MainMenu.java\" by method cmdUi.menu.MainMenu.setPilhaListView\nCaused by: "+rac$e);
  			   }
  			   if(!rac$b0) {
  			     if(rac$ErrorMsg.equals("")) {
  			       rac$ErrorMsg = "jml$ex";
  			     }
  			     else {
  			       rac$ErrorMsg += " and jml$ex";
  			     }
  			   }
  			   rac$b = rac$b && rac$b0;
           if(rac$ErrorMsg.indexOf("and") >= 0 ){
             rac$ErrorMsg += " are ";
           }
           else{
             rac$ErrorMsg += " is ";
           }
               JMLChecker.checkExceptionalPostcondition(rac$b,"by method cmdUi.menu.MainMenu.setPilhaListView regarding code at \nFile \"cmdUi.menu.MainMenu.java\""+"\n\t"+rac$ErrorMsg+rac$e, "jml$ex", true, -1, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".setPilhaListView(cmdUi.PilhaListView)", rac$e);
  		 }
  		   }
  	 }

  /** Generated by AspectJML to check non-static invariants of 
   * class MainMenu. */
  before (final cmdUi.menu.MainMenu object$rac) :
     (execution(!static * cmdUi.menu.MainMenu+.*(..))) && 
     !@annotation(JMLHelper) && 
     this(object$rac) {
         String invErrorMsg = "@pre <File \"MainMenu.java\"> regarding code at \nFile \"MainMenu.java\"\nnon_null for field 'plv' <File \"cmdUi.menu.MainMenu.java\", line 11, character 55 (cmdUi.menu.MainMenu.java:11)>";
         String evalErrorMsg = "Invalid expression in \"@pre <File \"MainMenu.java\"> regarding code at \nFile \"MainMenu.java\"\nnon_null for field 'plv' <File \"cmdUi.menu.MainMenu.java\", line 11, character 55 (cmdUi.menu.MainMenu.java:11)>\nCaused by: ";
         boolean rac$b = true;
         try {
          rac$b = (object$rac.plv != null);
         } catch (JMLNonExecutableException rac$nonExec) {
            rac$b = false;
         } catch (Throwable rac$cause) {
            if(rac$cause instanceof JMLAssertionError) {
             throw (JMLAssertionError) rac$cause;
            }
            else {
             throw new JMLEvaluationError(evalErrorMsg + rac$cause);
            }
         }
       JMLChecker.checkInvariant(rac$b, invErrorMsg, -1);

     }

  /** Generated by AspectJML to check the precondition of
   * method MainMenu. */
  before (final cmdUi.menu.MainMenu object$rac, final controller.Controller con, final int options) :
     execution(cmdUi.menu.MainMenu.new( controller.Controller, int )) && 
     this(object$rac) && args(con, options) {
       String preErrorMsg = "by method cmdUi.menu.MainMenu.<init> regarding specifications at \nFile \"cmdUi.menu.MainMenu.java\", [spec-case]: line 14, character 20 (cmdUi.menu.MainMenu.java:14), and \nby method cmdUi.menu.MainMenu.<init> regarding code at \nFile \"cmdUi.menu.MainMenu.java\""+", when \n"+"\t\'con\' is "+con;
       String evalErrorMsg = "Invalid expression in \"cmdUi.menu.MainMenu.java\" by method cmdUi.menu.MainMenu.<init> regarding specifications at \n[spec-case]: line 14, character 20 (cmdUi.menu.MainMenu.java:14)"+", when \n"+"\t\'con\' is "+con+"\nCaused by: ";
       boolean rac$b = true;
       try {
        rac$b = ((con != null) && true);
       } catch (JMLNonExecutableException rac$nonExec) {
          rac$b = false;
       } catch (Throwable rac$cause) {
          if(rac$cause instanceof JMLAssertionError) {
            throw (JMLAssertionError) rac$cause;
          }
          else {
            throw new JMLEvaluationError(evalErrorMsg + rac$cause);
          }
       }
       boolean canThrow = true;
       JMLChecker.checkPrecondition(rac$b, canThrow, preErrorMsg, -1, "cmdUi.menu.MainMenu.<init>(controller.Controller, int)");

     }

  /** Generated by AspectJML to check the precondition of
   * method setPilhaListView. */
  before (final cmdUi.menu.MainMenu object$rac, final cmdUi.PilhaListView plv) :
     (execution(void cmdUi.menu.MainMenu.setPilhaListView(cmdUi.PilhaListView))) && 
     this(object$rac) && args(plv) {
       String preErrorMsg = "by method cmdUi.menu.MainMenu.setPilhaListView regarding specifications at \nFile \"cmdUi.menu.MainMenu.java\", [spec-case]: line 87, character 30 (cmdUi.menu.MainMenu.java:87), and \nby method cmdUi.menu.MainMenu.setPilhaListView regarding code at \nFile \"cmdUi.menu.MainMenu.java\""+", when \n"+"\t\'plv\' is "+plv;
       String evalErrorMsg = "Invalid expression in \"cmdUi.menu.MainMenu.java\" by method cmdUi.menu.MainMenu.setPilhaListView regarding specifications at \n[spec-case]: line 87, character 30 (cmdUi.menu.MainMenu.java:87)"+", when \n"+"\t\'plv\' is "+plv+"\nCaused by: ";
       boolean rac$b = true;
       try {
        rac$b = ((plv != null) && (plv != null));
       } catch (JMLNonExecutableException rac$nonExec) {
          rac$b = false;
       } catch (Throwable rac$cause) {
          if(rac$cause instanceof JMLAssertionError) {
            throw (JMLAssertionError) rac$cause;
          }
          else {
            throw new JMLEvaluationError(evalErrorMsg + rac$cause);
          }
       }
       boolean canThrow = false;
       JMLChecker.checkPrecondition(rac$b, canThrow, preErrorMsg, -1, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".setPilhaListView(cmdUi.PilhaListView)");

     }


  /** Generated by AspectJML to check non-static invariants of 
   * class MainMenu. */
  after (final cmdUi.menu.MainMenu object$rac) :
     (execution(!static * cmdUi.menu.MainMenu+.*(..)) || 
       execution(cmdUi.menu.MainMenu+.new(..))) && 
     !execution(void cmdUi.menu.MainMenu.finalize() throws Throwable) && 
     !@annotation(JMLHelper) && 
     this(object$rac) {
       if (!(JMLChecker.hasAnyJMLError)) {
         String invErrorMsg = "@post <File \"MainMenu.java\"> regarding code at \nFile \"MainMenu.java\"\nnon_null for field 'plv' <File \"cmdUi.menu.MainMenu.java\", line 11, character 55 (cmdUi.menu.MainMenu.java:11)>";
         String evalErrorMsg = "Invalid expression in \"@post <File \"MainMenu.java\"> regarding code at \nFile \"MainMenu.java\"\nnon_null for field 'plv' <File \"cmdUi.menu.MainMenu.java\", line 11, character 55 (cmdUi.menu.MainMenu.java:11)>\nCaused by: ";
         boolean rac$b = true;
         try {
          rac$b = (object$rac.plv != null);
         } catch (JMLNonExecutableException rac$nonExec) {
            rac$b = false;
         } catch (Throwable rac$cause) {
          if(rac$cause instanceof JMLAssertionError) {
            throw (JMLAssertionError) rac$cause;
          }
          else {
            throw new JMLEvaluationError(evalErrorMsg + rac$cause);
          }
         }
         JMLChecker.checkInvariant(rac$b, invErrorMsg, -1);

       }
     }

  /** Generated by AspectJML to enable modular signals_only checking (XCS enabled) */
    after(final cmdUi.menu.MainMenu object$rac): (execution( * cmdUi.menu.MainMenu..*+.*(..))
            || execution(cmdUi.menu.MainMenu..*+.new(..))
            || execution( * cmdUi.menu.MainMenu+.*(..))
            || execution(cmdUi.menu.MainMenu+.new(..))) && 
     this(object$rac) {
     JMLChecker.hasAnyThrownExceptionalPostconditionSignalsOnly();
    }

  /** Generated by AspectJML to enhance error reporting (Execution Site enabled) */
    after() throwing (Throwable rac$e): (execution( * cmdUi.menu.MainMenu..*+.*(..))
            || execution(cmdUi.menu.MainMenu..*+.new(..))
            || execution( * cmdUi.menu.MainMenu+.*(..))
            || execution(cmdUi.menu.MainMenu+.new(..))){
      JMLChecker.hideAjmlSpecificStackTrace(rac$e);
    }

  /** Generated by AspectJML to enhance precondition checking */
  public static aspect UtilPreconditionChecking_MainMenu{
    before(): (execution( * cmdUi.menu.MainMenu..*+.*(..))
            || execution(cmdUi.menu.MainMenu..*+.new(..))
            || execution( * cmdUi.menu.MainMenu+.*(..))
            || execution(cmdUi.menu.MainMenu+.new(..))){
      JMLChecker.hasAnyThrownPrecondition();
    }
  }
}
