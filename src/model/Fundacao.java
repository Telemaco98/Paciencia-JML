package model;

import exception.PilhaVaziaException;
import util.Carta;
import util.Naipe;


public class Fundacao extends Pilha {

	public Fundacao() {
		super();
	}
	
	@Override
	protected /*@ pure @*/ boolean verificarCarta(Carta carta) {
		if (!carta.isParaCima()) return false;
		
		if (isEmpty()) {
			if (carta.getValor() == Carta.MENOR_VALOR) return true;
			return false;
		}
		
		Carta topo = null;
		try {
			topo = cartaTopo();
		} catch (PilhaVaziaException e) {
			System.out.println("Não há carta no topo");
		}
		
		if (topo.getValor()+1 == carta.getValor() && topo.getNaipe() == carta.getNaipe())
			return true;
		
		return false;
	}
	
	public static void main(String[] args) {
		Fundacao fundacao = new Fundacao();
		System.out.println(fundacao.isEmpty());
		System.out.println(fundacao.verificarCarta(new Carta(8, Naipe.PAUS)));
		
		try {
			System.out.println(fundacao.cartaTopo());
		} catch (PilhaVaziaException e) {
			System.out.println(e);
		}
		
		System.out.println(fundacao);
	}

}
