import cmdUi.menu.*;
import org.jmlspecs.ajmlrac.runtime.*;
import org.jmlspecs.lang.annotation.*;
import java.util.Scanner;
import cmdUi.Main;
import controller.Controller;
import java.util.Map;


privileged aspect AspectJMLRac_cmdUi_menu_AbstractMenu59e17edc_9fc6_4e7b_b1b9_90ed2662b97a {

 declare precedence: AspectJMLRac_*, *;




  /** Generated by AspectJML to check the exceptional postcondition of
   * method AbstractMenu. */
  after (final cmdUi.menu.AbstractMenu object$rac, final controller.Controller con, final int options, final cmdUi.menu.AbstractMenu parent) throwing (Throwable rac$e) :
     execution(cmdUi.menu.AbstractMenu.new( controller.Controller, int, cmdUi.menu.AbstractMenu.new )) && this(object$rac) && args(con, options, parent) {
           JMLChecker.rethrowJMLAssertionError(rac$e, "cmdUi.menu.AbstractMenu.<init>(controller.Controller, int, cmdUi.menu.AbstractMenu)");
           boolean rac$b = true;
           String rac$ErrorMsg = "";

  		   if (rac$b && (((con != null) && (parent != null)) && (parent != null))) {
  		     if (rac$e instanceof java.lang.RuntimeException) {
  			   java.lang.RuntimeException jml$ex = (java.lang.RuntimeException) rac$e;
  			   boolean rac$b0 = true;
  			   try{			     
  			     rac$b0 = true;
  			   }   catch (JMLNonExecutableException rac$nonExec) {
  			     throw new JMLEvaluationError("Invalid Expression in \"cmdUi.menu.AbstractMenu.java\" by method cmdUi.menu.AbstractMenu.<init>\nCaused by: "+rac$e);
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
               JMLChecker.checkExceptionalPostcondition(rac$b,"by method cmdUi.menu.AbstractMenu.<init> regarding code at \nFile \"cmdUi.menu.AbstractMenu.java\""+"\n\t"+rac$ErrorMsg+rac$e, "jml$ex", true, -1, "cmdUi.menu.AbstractMenu.<init>(controller.Controller, int, cmdUi.menu.AbstractMenu)", rac$e);
  		 }
  		   }
  	 }

  /** Generated by AspectJML to check the exceptional postcondition of
   * method draw. */
  after (final cmdUi.menu.AbstractMenu object$rac) throwing (Throwable rac$e) :
     (execution(void cmdUi.menu.AbstractMenu.draw())) && this(object$rac) {
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
  			     throw new JMLEvaluationError("Invalid Expression in \"cmdUi.menu.AbstractMenu.java\" by method cmdUi.menu.AbstractMenu.draw\nCaused by: "+rac$e);
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
               JMLChecker.checkExceptionalPostcondition(rac$b,"by method cmdUi.menu.AbstractMenu.draw regarding specifications at \nFile \"cmdUi.menu.AbstractMenu.java\""+"\n\t"+rac$ErrorMsg+rac$e, "jml$ex", true, -1, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".draw()", rac$e);
  		 }
  		   }
  	 }


  /** Generated by AspectJML to check the normal postcondition of
   * method processInput. */
  after (final cmdUi.menu.AbstractMenu object$rac, final int op) returning (final cmdUi.menu.AbstractMenu rac$result) :
     (execution(cmdUi.menu.AbstractMenu cmdUi.menu.AbstractMenu.processInput(int))) && this(object$rac) && args(op) {
       String nPostErrorMsg =  "";
       String evalErrorMsg = "";
       boolean rac$b = true;
         nPostErrorMsg =  "by method cmdUi.menu.AbstractMenu.processInput at \nFile \"cmdUi.menu.AbstractMenu.java\"";
         evalErrorMsg = "Invalid expression in \"cmdUi.menu.AbstractMenu.java\"\nCaused by: ";
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
  after (final cmdUi.menu.AbstractMenu object$rac, final int op) throwing (Throwable rac$e) :
     (execution(cmdUi.menu.AbstractMenu cmdUi.menu.AbstractMenu.processInput(int))) && this(object$rac) && args(op) {
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
  			     throw new JMLEvaluationError("Invalid Expression in \"cmdUi.menu.AbstractMenu.java\" by method cmdUi.menu.AbstractMenu.processInput\nCaused by: "+rac$e);
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
               JMLChecker.checkExceptionalPostcondition(rac$b,"by method cmdUi.menu.AbstractMenu.processInput regarding specifications at \nFile \"cmdUi.menu.AbstractMenu.java\""+"\n\t"+rac$ErrorMsg+rac$e, "jml$ex", true, -1, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".processInput(int)", rac$e);
  		 }
  		   }
  	 }


  /** Generated by AspectJML to check the exceptional postcondition of
   * method isOptionValid. */
  after (final cmdUi.menu.AbstractMenu object$rac, final int option) throwing (Throwable rac$e) :
     (execution(boolean cmdUi.menu.AbstractMenu.isOptionValid(int))) && this(object$rac) && args(option) {
           JMLChecker.rethrowJMLAssertionError(rac$e, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".isOptionValid(int)");
           boolean rac$b = true;
           String rac$ErrorMsg = "";

  		   if (true) {
  		     if (rac$e instanceof java.lang.RuntimeException) {
  			   java.lang.RuntimeException jml$ex = (java.lang.RuntimeException) rac$e;
  			   boolean rac$b0 = true;
  			   try{			     
  			     rac$b0 = true;
  			   }   catch (JMLNonExecutableException rac$nonExec) {
  			     throw new JMLEvaluationError("Invalid Expression in \"cmdUi.menu.AbstractMenu.java\" by method cmdUi.menu.AbstractMenu.isOptionValid\nCaused by: "+rac$e);
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
               JMLChecker.checkExceptionalPostcondition(rac$b,"by method cmdUi.menu.AbstractMenu.isOptionValid regarding code at \nFile \"cmdUi.menu.AbstractMenu.java\", line 29 (cmdUi.menu.AbstractMenu.java:29)"+"\n\t"+rac$ErrorMsg+rac$e, "jml$ex", true, -1, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".isOptionValid(int)", rac$e);
  		 }
  		   }
  	 }


  /** Generated by AspectJML to check the exceptional postcondition of
   * method getOptionInput. */
  after (final cmdUi.menu.AbstractMenu object$rac) throwing (Throwable rac$e) :
     (execution(int cmdUi.menu.AbstractMenu.getOptionInput())) && this(object$rac) {
           JMLChecker.rethrowJMLAssertionError(rac$e, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".getOptionInput()");
           boolean rac$b = true;
           String rac$ErrorMsg = "";

  		   if (true) {
  		     if (rac$e instanceof java.lang.RuntimeException) {
  			   java.lang.RuntimeException jml$ex = (java.lang.RuntimeException) rac$e;
  			   boolean rac$b0 = true;
  			   try{			     
  			     rac$b0 = true;
  			   }   catch (JMLNonExecutableException rac$nonExec) {
  			     throw new JMLEvaluationError("Invalid Expression in \"cmdUi.menu.AbstractMenu.java\" by method cmdUi.menu.AbstractMenu.getOptionInput\nCaused by: "+rac$e);
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
               JMLChecker.checkExceptionalPostcondition(rac$b,"by method cmdUi.menu.AbstractMenu.getOptionInput regarding code at \nFile \"cmdUi.menu.AbstractMenu.java\", line 42 (cmdUi.menu.AbstractMenu.java:42)"+"\n\t"+rac$ErrorMsg+rac$e, "jml$ex", true, -1, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".getOptionInput()", rac$e);
  		 }
  		   }
  	 }


  /** Generated by AspectJML to check non-static invariants of 
   * class AbstractMenu. */
  before (final cmdUi.menu.AbstractMenu object$rac) :
     (execution(!static * cmdUi.menu.AbstractMenu+.*(..))) && 
     !@annotation(JMLHelper) && 
     this(object$rac) {
         String invErrorMsg = "@pre <File \"AbstractMenu.java\"> regarding code at \nFile \"AbstractMenu.java\"\nnon_null for field 'sc' <File \"cmdUi.menu.AbstractMenu.java\", line 12, character 30 (cmdUi.menu.AbstractMenu.java:12)>";
         String evalErrorMsg = "Invalid expression in \"@pre <File \"AbstractMenu.java\"> regarding code at \nFile \"AbstractMenu.java\"\nnon_null for field 'sc' <File \"cmdUi.menu.AbstractMenu.java\", line 12, character 30 (cmdUi.menu.AbstractMenu.java:12)>\nCaused by: ";
         boolean rac$b = true;
         try {
          rac$b = (object$rac.sc != null);
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
   * method AbstractMenu. */
  before (final cmdUi.menu.AbstractMenu object$rac, final controller.Controller con, final int options, final cmdUi.menu.AbstractMenu parent) :
     execution(cmdUi.menu.AbstractMenu.new( controller.Controller, int, cmdUi.menu.AbstractMenu.new )) && 
     this(object$rac) && args(con, options, parent) {
       String preErrorMsg = "by method cmdUi.menu.AbstractMenu.<init> regarding specifications at \nFile \"cmdUi.menu.AbstractMenu.java\", [spec-case]: line 16, character 42 (cmdUi.menu.AbstractMenu.java:16), line 14, character 31 (cmdUi.menu.AbstractMenu.java:14), and \nby method cmdUi.menu.AbstractMenu.<init> regarding code at \nFile \"cmdUi.menu.AbstractMenu.java\""+", when \n"+"\t\'con\' is "+con+"\n\t\'parent\' is "+parent;
       String evalErrorMsg = "Invalid expression in \"cmdUi.menu.AbstractMenu.java\" by method cmdUi.menu.AbstractMenu.<init> regarding specifications at \n[spec-case]: line 16, character 42 (cmdUi.menu.AbstractMenu.java:16), line 14, character 31 (cmdUi.menu.AbstractMenu.java:14)"+", when \n"+"\t\'con\' is "+con+"\n\t\'parent\' is "+parent+"\nCaused by: ";
       boolean rac$b = true;
       try {
        rac$b = (((con != null) && (parent != null)) && (parent != null));
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
       JMLChecker.checkPrecondition(rac$b, canThrow, preErrorMsg, -1, "cmdUi.menu.AbstractMenu.<init>(controller.Controller, int, cmdUi.menu.AbstractMenu)");

     }


  /** Generated by AspectJML to check non-static invariants of 
   * class AbstractMenu. */
  after (final cmdUi.menu.AbstractMenu object$rac) :
     (execution(!static * cmdUi.menu.AbstractMenu+.*(..)) || 
       (execution(cmdUi.menu.AbstractMenu+.new(..)) && !within(cmdUi.menu.AbstractMenu))) && 
     !execution(void cmdUi.menu.AbstractMenu.finalize() throws Throwable) && 
     !@annotation(JMLHelper) && 
     this(object$rac) {
       if (!(JMLChecker.hasAnyJMLError)) {
         String invErrorMsg = "@post <File \"AbstractMenu.java\"> regarding code at \nFile \"AbstractMenu.java\"\nnon_null for field 'sc' <File \"cmdUi.menu.AbstractMenu.java\", line 12, character 30 (cmdUi.menu.AbstractMenu.java:12)>";
         String evalErrorMsg = "Invalid expression in \"@post <File \"AbstractMenu.java\"> regarding code at \nFile \"AbstractMenu.java\"\nnon_null for field 'sc' <File \"cmdUi.menu.AbstractMenu.java\", line 12, character 30 (cmdUi.menu.AbstractMenu.java:12)>\nCaused by: ";
         boolean rac$b = true;
         try {
          rac$b = (object$rac.sc != null);
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
    after(final cmdUi.menu.AbstractMenu object$rac): (execution( * cmdUi.menu.AbstractMenu..*+.*(..))
            || execution(cmdUi.menu.AbstractMenu..*+.new(..))
            || execution( * cmdUi.menu.AbstractMenu+.*(..))
            || execution(cmdUi.menu.AbstractMenu+.new(..))) && 
     this(object$rac) {
     JMLChecker.hasAnyThrownExceptionalPostconditionSignalsOnly();
    }

  /** Generated by AspectJML to enhance error reporting (Execution Site enabled) */
    after() throwing (Throwable rac$e): (execution( * cmdUi.menu.AbstractMenu..*+.*(..))
            || execution(cmdUi.menu.AbstractMenu..*+.new(..))
            || execution( * cmdUi.menu.AbstractMenu+.*(..))
            || execution(cmdUi.menu.AbstractMenu+.new(..))){
      JMLChecker.hideAjmlSpecificStackTrace(rac$e);
    }
}