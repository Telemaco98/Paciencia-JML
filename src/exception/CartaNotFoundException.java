package exception;

public class CartaNotFoundException extends Exception {
	private static final long serialVersionUID = 1L;

	public CartaNotFoundException() {
		super();
	}
	
	public CartaNotFoundException (String msg) {
		super (msg);
	}
}