import model.*;
import org.jmlspecs.ajmlrac.runtime.*;
import org.jmlspecs.lang.annotation.*;
import util.Carta;
import java.util.Map;


privileged aspect AspectJMLRac_model_Fundacao5e3f91b4_4867_45ee_9161_18fd9d97e950 {

 declare precedence: AspectJMLRac_*, *;

  /** Generated by AspectJML to check the exceptional postcondition of
   * method Fundacao. */
  after (final model.Fundacao object$rac) throwing (Throwable rac$e) :
     execution(model.Fundacao.new(  )) && this(object$rac) {
           JMLChecker.rethrowJMLAssertionError(rac$e, "model.Fundacao.<init>()");
           boolean rac$b = true;
           String rac$ErrorMsg = "";

  		   if (true) {
  		     if (rac$e instanceof java.lang.RuntimeException) {
  			   java.lang.RuntimeException jml$ex = (java.lang.RuntimeException) rac$e;
  			   boolean rac$b0 = true;
  			   try{			     
  			     rac$b0 = true;
  			   }   catch (JMLNonExecutableException rac$nonExec) {
  			     throw new JMLEvaluationError("Invalid Expression in \"model.Fundacao.java\" by method model.Fundacao.<init>\nCaused by: "+rac$e);
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
               JMLChecker.checkExceptionalPostcondition(rac$b,"by method model.Fundacao.<init> regarding code at \nFile \"model.Fundacao.java\""+"\n\t"+rac$ErrorMsg+rac$e, "jml$ex", true, -1, "model.Fundacao.<init>()", rac$e);
  		 }
  		   }
  	 }


  /** Generated by AspectJML to check the exceptional postcondition of
   * method verificarCarta. */
  after (final model.Fundacao object$rac, final util.Carta carta) throwing (Throwable rac$e) :
     (execution(boolean model.Fundacao.verificarCarta(util.Carta))) && this(object$rac) && args(carta) {
           JMLChecker.rethrowJMLAssertionError(rac$e, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".verificarCarta(util.Carta)");
           boolean rac$b = true;
           String rac$ErrorMsg = "";

  		   if (true) {
  		     if (rac$e instanceof java.lang.RuntimeException) {
  			   java.lang.RuntimeException jml$ex = (java.lang.RuntimeException) rac$e;
  			   boolean rac$b0 = true;
  			   try{			     
  			     rac$b0 = true;
  			   }   catch (JMLNonExecutableException rac$nonExec) {
  			     throw new JMLEvaluationError("Invalid Expression in \"model.Fundacao.java\" by method model.Fundacao.verificarCarta\nCaused by: "+rac$e);
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
               JMLChecker.checkExceptionalPostcondition(rac$b,"by method model.Fundacao.verificarCarta regarding code at \nFile \"model.Fundacao.java\", line 28 (model.Fundacao.java:28)"+"\n\t"+rac$ErrorMsg+rac$e, "jml$ex", true, -1, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".verificarCarta(util.Carta)", rac$e);
  		 }
  		   }
  	 }



  /** Generated by AspectJML to check the precondition of
   * method verificarCarta. */
  before (final model.Fundacao object$rac, final util.Carta carta) :
     (execution(boolean model.Fundacao.verificarCarta(util.Carta))) && 
     this(object$rac) && args(carta) {
       String preErrorMsg = "by method model.Fundacao.verificarCarta regarding code at \nFile \"model.Fundacao.java\", line 28 (model.Fundacao.java:28)"+", when \n"+"\t\'carta\' is "+carta;
       String evalErrorMsg = "Invalid expression in \"model.Fundacao.java\"\nCaused by: ";
       boolean rac$b = true;
       try {
        rac$b = (carta != null);
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
       JMLChecker.checkPrecondition(rac$b, canThrow, preErrorMsg, -1, object$rac.getClass().getName() + "@" + Integer.toHexString(System.identityHashCode(object$rac))+".verificarCarta(util.Carta)");

     }



  /** Generated by AspectJML to enable modular signals_only checking (XCS enabled) */
    after(final model.Fundacao object$rac): (execution( * model.Fundacao..*+.*(..))
            || execution(model.Fundacao..*+.new(..))
            || execution( * model.Fundacao+.*(..))
            || execution(model.Fundacao+.new(..))) && 
     this(object$rac) {
     JMLChecker.hasAnyThrownExceptionalPostconditionSignalsOnly();
    }

  /** Generated by AspectJML to enhance error reporting (Execution Site enabled) */
    after() throwing (Throwable rac$e): (execution( * model.Fundacao..*+.*(..))
            || execution(model.Fundacao..*+.new(..))
            || execution( * model.Fundacao+.*(..))
            || execution(model.Fundacao+.new(..))){
      JMLChecker.hideAjmlSpecificStackTrace(rac$e);
    }

  /** Generated by AspectJML to enhance precondition checking */
  public static aspect UtilPreconditionChecking_Fundacao{
    before(): (execution( * model.Fundacao..*+.*(..))
            || execution(model.Fundacao..*+.new(..))
            || execution( * model.Fundacao+.*(..))
            || execution(model.Fundacao+.new(..))){
      JMLChecker.hasAnyThrownPrecondition();
    }
  }
}
