package config;

/**Configurações gerais do jogo.
 * Padrão Singleton*/
public class Configuracao {

	public static final int PUXAR_UMA_CARTA = 0;
	public static final int PUXAR_TRES_CARTAS = 1;
	
	/**Representa o modo como as cartas serão puxadas do estoque*/
	private /*@ spec_public @*/ int modoPuxarCartasEstoque; 
	
	private static /*@ spec_public nullable @*/ Configuracao config = null;
	
	/*@ assignable this.modoPuxarCartasEstoque;
	  @ ensures    this.modoPuxarCartasEstoque == PUXAR_UMA_CARTA; 
	  @*/
	private Configuracao () {
		modoPuxarCartasEstoque = PUXAR_UMA_CARTA;
	}
	
	public /*@ pure @*/ static Configuracao getInstance() {
		if (config == null) config = new Configuracao();
		return config;
	}
	
	/*@ requires modo == 1 || modo == 0;
	  @ assignable this.modoPuxarCartasEstoque;
	  @ ensures    this.modoPuxarCartasEstoque == modo;
	  @ ensures    this.modoPuxarCartasEstoque == 1 || this.modoPuxarCartasEstoque == 0; 
	  @*/
	public void setModoEstoque(int modo) {
		modoPuxarCartasEstoque = modo;
	}
	
	public /*@ pure @*/ int getQtdCartasPuxadasEstoque() {
		switch (modoPuxarCartasEstoque) {
			case PUXAR_UMA_CARTA: return 1;
			case PUXAR_TRES_CARTAS: return 3;
			default: return 1;
		}
	}
	
	public static void main(String[] args) {
		Configuracao config = new Configuracao();
		System.out.println(Configuracao.getInstance());
		config.setModoEstoque(1);
		System.out.println(config.getQtdCartasPuxadasEstoque());
		config.setModoEstoque(0);
		System.out.println(config.getQtdCartasPuxadasEstoque());
		}
}
