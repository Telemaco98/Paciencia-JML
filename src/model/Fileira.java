package model;

import java.util.ArrayList;

import exception.PilhaVaziaException;
import util.Carta;
import util.Naipe;

/**Representa uma Pilha Fileira do jogo Paciência. 
 * Esta pilha possui cartas viradas para baixo e para cima. 
 * Suas condições para receber novas cartas são:
 * 	- Pilha vazia e carta recebida Rei;
 *  - Carta do topo virada para cima, e carta recebida 1 valor abaixo do topo e de cor diferente.*/
public class Fileira extends Pilha{
	
	public Fileira() {
		super();
	}
	
	/*@ requires cartasParaBaixo != null;
	  @ assignable this.cartas; */
	public Fileira(ArrayList<Carta> cartasParaBaixo) {
		this();
		cartas.addAll(cartasParaBaixo);
	}

	@Override
	protected /*@ pure @*/ boolean verificarCarta(Carta carta) {
		if (!carta.isParaCima()) return false;
		
		if (isEmpty()) {
			if (carta.getValor() == Carta.MAIOR_VALOR) return true;
			return false;
		}
		
		Carta topo = null;
		try {
			topo = cartaTopo();
		} catch (PilhaVaziaException e) {
			System.out.println("Não há carta no topo");
		}
		
		if (!topo.isParaCima()) return false;
		
		if (topo.getValor()-1 == carta.getValor() && topo.getColor() != carta.getColor())
			return true;
		
		return false;
	}
	
	public static void main(String[] args) {
		Fileira fileira = new Fileira();
		System.out.println(fileira.isEmpty());
		System.out.println(fileira.verificarCarta(new Carta(8, Naipe.PAUS)));
		
		try {
			System.out.println(fileira.cartaTopo());
		} catch (PilhaVaziaException e) {
			System.out.println(e);
		}
		
		ArrayList<Carta> cartasPbaixo = new ArrayList<>();
		cartasPbaixo.add(new Carta(9, Naipe.COPAS));
		cartasPbaixo.add(new Carta(1, Naipe.OURO));
		cartasPbaixo.add(new Carta(Carta.AS, Naipe.PAUS));
		cartasPbaixo.add(new Carta(Carta.K, Naipe.ESPADA));
		fileira = new Fileira(cartasPbaixo);
		
		System.out.println(fileira);
	}

}
