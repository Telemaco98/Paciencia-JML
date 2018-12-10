package cmdUi;

import java.util.ArrayList;

import model.Pilha;
import util.Carta;

/**Cuida da visualização das pilhas em linha de comando*/
public class PilhaListView {

	private /*@ spec_public @*/ ArrayList<Pilha> pilhas;
	
	/*@ requires pilhas != null;
	  @ assignable this.pilhas;
	  @ ensures (\forall int i; 0 <= i && i < pilhas.size(); pilhas.get(i) == this.pilhas.get(i));
	  @*/
	public PilhaListView (ArrayList<Pilha> pilhas) {
		this.pilhas = pilhas;
	}
	
	public /*@ pure @*/ ArrayList<Pilha> getPilhas() {
		return pilhas;
	}

	/*@ requires pilhas != null;
	  @ assignable this.pilhas;
	  @ ensures (\forall int i; 0 <= i && i < pilhas.size(); pilhas.get(i) == this.pilhas.get(i));
	  @*/
	public void setPilhas(ArrayList<Pilha> pilhas) {
		this.pilhas = pilhas;
	}

	public /*@ pure @*/ void drawPilhas() {
		
		int index = 1;
		for (Pilha pilha: pilhas) {
			Main.print((index++)+" - ");
			Main.print(pilha.getClass().getName().toUpperCase().split("[.]")[1]);
			Main.print(" == "+drawCards(pilha));
			Main.print("\n");
		}
		Main.print("\n");
	}
	
	public /*@ pure @*/ String drawCards(Pilha pilha) {
		StringBuilder sb = new StringBuilder();
		Carta[] cartas = pilha.getCartas();
		
		String paraBaixo = "[<>]";
		String valor;
		
		boolean first = true;
		for (Carta carta: cartas) {
			switch (carta.getValor()) {
			case Carta.K: valor ="K "; break;
			case Carta.Q: valor ="Q "; break;
			case Carta.J: valor = "J "; break;
			case Carta.AS: valor = "AS "; break;
			default: valor = carta.getValor()+" "; break;
			}
			
			valor += carta.getNaipe().name();
			
			if (first) {
				first = false;
			} else sb.append(", ");
			
			if (carta.isParaCima()) {
				sb.append(valor);
			} else sb.append(paraBaixo);
			
			
		}
		return sb.toString();
	}
}
