package util;

import java.awt.Color;

/**
 * Class representando uma carta de um baralho
 * @author Heitor e Ivan
 * */
public class Carta implements Comparable<Carta> {
	/**Valor da carta*/
	private /*@ spec_public @*/ int valor;
	/**Naipe da carta*/
	private /*@ spec_public @*/ Naipe naipe;

	/**Define se a carta está para cima ou para baixo*/
	private /*@ spec_public @*/ boolean paraCima;
	
	/**Valor do Rei*/
	public static final int K = 13;
	/**Valor da Rainha*/
	public static final int Q = 12;
	/**Valor do Valete*/
	public static final int J = 11;
	/**Valor do As*/
	public static final int AS = 1;
	
	/**Maior valor do jogo*/
	public static final int MAIOR_VALOR = K;
	/**Menor valor do jogo*/
	public static final int MENOR_VALOR = AS;
	
	/*@ requires 1 <= valor && valor <= 13;
	  @ requires naipe != null;
	  @ assignable this.valor;
	  @ assignable this.naipe;
	  @*/
	public Carta (int valor, Naipe naipe) {
		this.valor = valor;
		this.naipe = naipe;
		paraCima = false;
	}
		
	public /*@ pure @*/ Color getColor() {
		return naipe.getColor();
	}

	
	public /*@ pure @*/ int getValor() {
		return valor;
	}

	/*@ assignable this.valor;
	  @ ensures this.valor == valor;
	  @*/
	public void setValor(int valor) {
		this.valor = valor;
	}

	public /*@ pure @*/ Naipe getNaipe() {
		return naipe;
	}

	/*@ assignable this.naipe;
	  @ ensures this.naipe == naipe; 
	  @*/
	public void setNaipe(Naipe naipe) {
		this.naipe = naipe;
	}
	
	public /*@ pure @*/ boolean isParaCima() {
		return paraCima;
	}

	/** Change the paraCima variable value */
	/*@ assignable paraCima;
	  @ ensures this.paraCima == !(\old(this.paraCima));
	  @*/
	public void virarCarta() {
		paraCima = !paraCima;
	}
	
	public /*@ pure @*/ boolean isMaiorValor () {
		return valor == MAIOR_VALOR;
	}
	
	public /*@ pure @*/ boolean isMenorValor() {
		return valor == MENOR_VALOR;
	}
	
	/**Retorna uma representação de carta para baixo se paraCima for false,
	 * ou o valor da carta seguido do Naipe caso paraCima seja true.
	 * 
	 * @return String que representa a carta*/
	public /*@ pure @*/ String toString() {
		if (!isParaCima()) {
			return "[<>]";
		} 
		else {
			String str = "";
			if (valor == K) str += "K";
			else if (valor == Q) str += "Q";
			else if (valor == J) str += "J";
			else if (valor == AS) str += "AS";
			else str += valor;
			
			str += " " +naipe.name();
			return str;
		}
	}

	@Override
	public /*@ pure @*/ int compareTo(Carta o) {
		if (this.valor == o.getValor()) return 0;
		if (this.valor > o.getValor()) return 1;
		else return -1;
	}
	
	public static void main(String[] args) {
		Carta carta = new Carta(J, Naipe.OURO);
		System.out.println(carta.getColor());
		System.out.println(carta.getValor());
		carta.setValor(10);
		carta.setNaipe(Naipe.COPAS);
		System.out.println(carta.isParaCima());
		carta.virarCarta();
		System.out.println(carta.isMaiorValor());
		System.out.println(carta.isMenorValor());
		System.out.println(carta);
	}	
}
