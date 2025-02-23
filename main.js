function scrollToHash() {
  if (window.location.hash === '') return;

  const id = window.location.hash.slice(1);

  // #id doesn't work with numerical IDs
  const elem = document.querySelector(`[id="${id}"]`);
  if (!elem) return;

  // If the element is in a <details> tag, open it and scroll to it.
  const details = elem.closest('details');
  if (details) {
    details.setAttribute("open", "");
    elem.scrollIntoView();
  }
}

window.addEventListener("DOMContentLoaded", scrollToHash);
window.addEventListener("hashchange", scrollToHash);
