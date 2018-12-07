package model;

import java.util.ArrayList;

import exception.PilhaVaziaException;
import util.Carta;
import util.Naipe;

public class Estoque extends Pilha {

	public Estoque() {
		super();
	}
	
	/*@ requires cartasParaBaixo != null;
	  @ assignable this.cartas; */
	public Estoque(ArrayList<Carta> cartasParaBaixo) {
		this();
		cartas.addAll(cartasParaBaixo);
	}
	
	@Override
	protected /*@ pure @*/ boolean verificarCarta(Carta carta) {
		return false;
	}
	
	public static void main(String[] args) {
		Estoque estoque = new Estoque();
		System.out.println(estoque.isEmpty());
		System.out.println(estoque.verificarCarta(new Carta(8, Naipe.PAUS)));
		
		try {
			System.out.println(estoque.cartaTopo());
		} catch (PilhaVaziaException e) {
			System.out.println(e);
		}
		
		ArrayList<Carta> cartasPbaixo = new ArrayList<>();
		cartasPbaixo.add(new Carta(9, Naipe.COPAS));
		cartasPbaixo.add(new Carta(1, Naipe.OURO));
		cartasPbaixo.add(new Carta(Carta.AS, Naipe.PAUS));
		cartasPbaixo.add(new Carta(Carta.K, Naipe.ESPADA));
		estoque = new Estoque(cartasPbaixo);
		
		System.out.println(estoque);
	}

}
