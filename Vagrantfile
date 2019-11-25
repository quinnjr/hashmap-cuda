# -*- mode: ruby -*-
# vi: set ft=ruby :

Vagrant.configure("2") do |config|
  config.vm.box = "quinnjr/archlinux-ansible"

  config.vm.synced_folder "./", "/home/vagrant/Project",
   create: true

  config.vm.provider "virtualbox" do |vb|
    vb.memory = "1024"
  end

  config.vm.provision "shell", inline: <<-SHELL
    pacman -Syu --noconfirm --needed
    pacman -S --noconfirm --needed base-devel git ccache clang llvm rustup cuda pkg-config openssl
    su - vagrant -c "/usr/bin/rustup default nightly"
    su - vagrant -c "cargo install cargo-edit >/dev/null"
  SHELL
end
