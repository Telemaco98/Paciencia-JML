package exception;

public class PilhaVaziaException extends RuntimeException {
	private static final long serialVersionUID = 1L;

	public /*@ pure @*/ PilhaVaziaException() {
		super();
	}
	
	public PilhaVaziaException (String msg) {
		super (msg);
	}
}
